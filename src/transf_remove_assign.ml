(*************************************************************
 *                                                           *
 *       Cryptographic protocol verifier                     *
 *                                                           *
 *       Bruno Blanchet and David Cadé                       *
 *                                                           *
 *       Copyright (C) ENS, CNRS, INRIA, 2005-2014           *
 *                                                           *
 *************************************************************)

(*

    Copyright ENS, CNRS, INRIA 
    contributors: Bruno Blanchet, Bruno.Blanchet@inria.fr
                  David Cadé

This software is a computer program whose purpose is to verify 
cryptographic protocols in the computational model.

This software is governed by the CeCILL-B license under French law and
abiding by the rules of distribution of free software.  You can  use, 
modify and/ or redistribute the software under the terms of the CeCILL-B
license as circulated by CEA, CNRS and INRIA at the following URL
"http://www.cecill.info". 

As a counterpart to the access to the source code and  rights to copy,
modify and redistribute granted by the license, users are provided only
with a limited warranty  and the software's author,  the holder of the
economic rights,  and the successive licensors  have only  limited
liability. 

In this respect, the user's attention is drawn to the risks associated
with loading,  using,  modifying and/or developing or reproducing the
software by the user in light of its specific status of free software,
that may mean  that it is complicated to manipulate,  and  that  also
therefore means  that it is reserved for developers  and  experienced
professionals having in-depth computer knowledge. Users are therefore
encouraged to load and test the software's suitability as regards their
requirements in conditions enabling the security of their systems and/or 
data to be ensured and,  more generally, to use and operate it in the 
same conditions as regards security. 

The fact that you are presently reading this means that you have had
knowledge of the CeCILL-B license and that you accept its terms.

*)
open Types

(* Remove assignments 

This transformation assumes that LetE/FindE/TestE/ResE occur only in 
conditions of find, which is guaranteed after expansion.
(In fact, it supports them as well in channel names, conditions of tests, events,
outputs, although that's not necessary.)
It also assumes (and checks) that variables defined in conditions of find
have no array references and do not occur in queries.

Note that it is important that there are no LetE or FindE in let
expressions or in patterns! Otherwise, we should verify for each
expression that we copy that it does not contain LetE or FindE: if we
copy a LetE or FindE, we may break the invariant that each variable is
assigned at most once.

Be careful of variables defined at several places!  *)

let replacement_def_list = ref []
(* List of correspondences (b,b'), b = old binder, b' = new binder,
   for defined conditions. When b is used only in "defined" conditions,
   we try to find another binder b' defined in the same cases, so that
   we can remove the definition of b completely. *)

let done_transfos = ref []

let done_sa_rename = ref []

(* Function for assignment expansion for terms *)

let expand_assign_term let_t remove_set
    rec_simplif pat t p1 topt =
  match pat with
    PatEqual t' -> 
      Settings.changed := true;
      done_transfos := (DLetESimplifyPattern(let_t, pat, DEqTest)) :: (!done_transfos);
      Terms.build_term_type p1.t_type (TestE(Terms.make_equal t t', rec_simplif p1, 
	    match topt with
	      None -> Parsing_helper.internal_error "Missing else part of let"
	    | Some p2 -> rec_simplif p2))
  | PatTuple (f,l) -> 
      (* try to split *)
      begin
	try 
	  let res = rec_simplif
	      (Terms.put_lets_term l (Terms.split_term f t) p1 topt)
	  in
	  Settings.changed := true;
          done_transfos := (DLetESimplifyPattern(let_t, pat, DExpandTuple)) :: (!done_transfos);
	  res
	with Not_found -> 
	  Terms.build_term_type p1.t_type (LetE(pat, t, rec_simplif p1, match topt with 
	    None -> None
	  | Some p2 -> Some (rec_simplif p2)))
	| Terms.Impossible -> 
	    Settings.changed := true;
            done_transfos := (DLetESimplifyPattern(let_t, pat, DImpossibleTuple)) :: (!done_transfos);
	    match topt with
	      None -> Parsing_helper.internal_error "Missing else part of let"
	    | Some p2 -> rec_simplif p2
      end
  | PatVar b ->
      if Terms.has_array_ref_q b then
	Parsing_helper.internal_error "Variables defined in conditions of find should not have array references and should not occur in queries.";
      if not (Terms.check_no_ifletfindres t) then
	Parsing_helper.internal_error "If, find, let, and new should not occur in expand_assign";
      let put_link() =
	if Terms.refers_to b t then
	  (* Cannot replace cyclic assignment *)
	  Terms.build_term_type p1.t_type (LetE(pat, t, rec_simplif p1, None))
	else 
          begin
                (* copy_term exactly replaces 
                   b[b.args_at_creation] with t, without changing any other variable.
                   (Changing other variables led to a bug, because it replaced
                   v[v.args_at_creation] with its value in a "defined" condition,
                   even when v is defined less often than its value.) *)
            let p1' = Terms.copy_term (Terms.OneSubst(b,t,ref false)) p1 in
	    Settings.changed := true;
            done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
	    rec_simplif p1'
          end
      in
      if (not (Terms.refers_to b p1)) then
	begin
	  (* Variable is useless *)
	  Settings.changed := true;
          done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
	  rec_simplif p1
	end
      else
	match remove_set with
	  All -> put_link()
	| OneBinder b0 when b == b0 -> put_link()
	| _ -> 
	    match t.t_desc with
	      Var _ | ReplIndex _ when !Settings.expand_letxy -> 
		put_link()
	    | _ ->
		Terms.build_term_type p1.t_type (LetE(pat, t, rec_simplif p1, None))

(* Function for assignment expansion for processes *)

let candidate_for_rem_assign remove_set b t p =
  if not (Terms.refers_to_process_nodef b p || b.array_ref || Settings.occurs_in_queries b) then
    true
  else
  match remove_set with
    All -> true
  | OneBinder b0 when b == b0 -> true
  | _ -> 
      match t.t_desc with
	Var _ | ReplIndex _ when !Settings.expand_letxy -> true
      | _ -> false

let rec find_replacement_for_def remove_set b p =
  match p.p_desc with
    Yield | EventAbort _ -> raise Not_found
  | Restr(b',p') ->
      if b' != b && b'.count_def == 1 then b' else find_replacement_for_def remove_set b p'
  | Let(PatVar b', t, p', _) ->
      if b' != b && b'.count_def == 1 && not (candidate_for_rem_assign remove_set b' t p') then b' else 
      find_replacement_for_def remove_set b p'
  | EventP(_,p') -> find_replacement_for_def remove_set b p'
  | Test _ | Find _ | Output _ | Let _ -> raise Not_found
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"


let expand_assign let_p remove_set above_proc rec_simplif pat t p1 p2 =
  match pat with
    PatEqual t' -> 
      Settings.changed := true;
      done_transfos := (DLetSimplifyPattern(let_p, pat, DEqTest)) :: (!done_transfos);
      Terms.oproc_from_desc (Test(Terms.make_equal t t', rec_simplif p1 p1, rec_simplif p2 p2))
  | PatTuple (f,l) -> 
      (* try to split *)
      begin
	try 
          let p' = (Terms.put_lets l (Terms.split_term f t) p1 p2) in
	  let res = rec_simplif p' p' in
          done_transfos := (DLetSimplifyPattern(let_p, pat, DExpandTuple)) :: (!done_transfos);
	  Settings.changed := true;
	  res
	with Not_found -> 
	  Terms.oproc_from_desc (Let(pat, t, rec_simplif p1 p1, rec_simplif p2 p2))
	| Terms.Impossible -> 
            done_transfos := (DLetSimplifyPattern(let_p, pat, DImpossibleTuple)) :: (!done_transfos);
	    Settings.changed := true;
	    rec_simplif p2 p2
      end
  | PatVar b ->
      let put_link do_advise =
	if Terms.refers_to b t then
	  (* Cannot replace cyclic assignment *)
	  Terms.oproc_from_desc (Let(pat, t, rec_simplif above_proc p1, Terms.oproc_from_desc Yield))
	else 
	  match b.def with
	    [] -> Parsing_helper.internal_error "Should have at least one definition"
	  | [d] -> (* There is a single definition *)
	      begin
		(* All references to binder b will be removed *)
		Terms.link b (TLink t);
		if Settings.occurs_in_queries b then
		  (* if b occurs in queries then leave as it is *)
		  Terms.oproc_from_desc (Let(pat, t, rec_simplif above_proc p1, Terms.oproc_from_desc Yield))
		else if b.root_def_array_ref || b.root_def_std_ref || b.array_ref then
		  (* We may keep calls to defined(b), so keep a definition of b
		     but its value does not matter *)
                  try
                    (* Try to remove the definition of b completely, by replacing
                       defined(b[...]) with defined(b'[...]) *)
                    let b' = find_replacement_for_def remove_set b above_proc in
                    Settings.changed := true;
                    done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
                    replacement_def_list := (b, b') :: (!replacement_def_list);
                    rec_simplif above_proc p1
                  with Not_found ->
		    let t' = Terms.cst_for_type t.t_type in
		    if not (Terms.equal_terms t t') then 
                      begin
                        done_transfos := (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: (!done_transfos);
                        Settings.changed := true
                      end;
		    Terms.oproc_from_desc (Let(pat,  t', rec_simplif above_proc p1, Terms.oproc_from_desc Yield))
		else
		  begin
                    (* b will completely disappear *)
                    Settings.changed := true;
                    done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
		    rec_simplif above_proc p1
		  end
	      end
	  | _ -> (* There are several definitions.
		    I can remove in-scope requests, but out-of-scope array accesses will remain *)
              begin
                (* copy_oprocess exactly replaces 
                   b[b.args_at_creation] with t, without changing any other variable.
                   (Changing other variables led to a bug, because it replaced
                   v[v.args_at_creation] with its value in a "defined" condition,
                   even when v is defined less often than its value.) *)
                let copy_changed = ref false in
                let p1' = Terms.copy_oprocess (Terms.OneSubst(b,t,copy_changed)) p1 in
                let subst_def = !copy_changed in (* Set to true if an occurrence of b has really been substituted *)
                Settings.changed := (!Settings.changed) || subst_def;
                let p1'' = rec_simplif above_proc p1' in
                if b.array_ref then
		  begin
                    (* suggest to use "sa_rename b" before removing assignments *)
		    if do_advise then Settings.advise := Terms.add_eq (SArenaming b) (!Settings.advise);
                    (* Keep the definition so that out-of-scope array accesses are correct *)
                    if subst_def then
                      done_transfos := (DRemoveAssign(b, DKeepDef, DRemoveNonArray)) :: (!done_transfos);
                    Terms.oproc_from_desc (Let(pat, t, p1'', Terms.oproc_from_desc Yield))
		  end
		else if Settings.occurs_in_queries b then
                  begin
		    (* Cannot change definition if b occurs in queries *)
                    if subst_def then
                      done_transfos := (DRemoveAssign(b, DKeepDef, DRemoveAll)) :: (!done_transfos);
 		    Terms.oproc_from_desc (Let(pat, t, p1'', Terms.oproc_from_desc Yield))
                  end
                else if b.root_def_array_ref || b.root_def_std_ref then
		  (* We may keep calls to defined(b), so keep a definition of b
		     but its value does not matter *)
		  let t' = Terms.cst_for_type t.t_type in
		  if not (Terms.equal_terms t t') then 
                    begin
                      done_transfos := (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: (!done_transfos);
                      Settings.changed := true
                    end
                  else if subst_def then
                    done_transfos := (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: (!done_transfos);
		  Terms.oproc_from_desc (Let(pat, t', p1'', Terms.oproc_from_desc Yield))
		else
                  (* b will completely disappear *)
		  begin
                    done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
		    Settings.changed := true;
		    p1''
		  end
              end
      in
      if (Terms.check_no_ifletfindres t) then
	begin
	  if not (Terms.refers_to_process_nodef b p1 || b.array_ref || Settings.occurs_in_queries b) then
	    begin
	      (* Value of the variable is useless *)
	      if not (b.root_def_std_ref || b.root_def_array_ref) then
	        (* Variable is useless *)
		begin
		  Settings.changed := true;
                  done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
		  rec_simplif above_proc p1
		end
	      else
		begin
	          (* We may keep calls to defined(b), so keep a definition of b
		     but its value does not matter *)
                  try
                    (* Try to remove the definition of b completely, by replacing
                       defined(b[...]) with defined(b'[...]) *)
                    if b.count_def > 1 then raise Not_found;
                    let b' = find_replacement_for_def remove_set b above_proc in
                    Settings.changed := true;
                    done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
                    replacement_def_list := (b, b') :: (!replacement_def_list);
                    rec_simplif above_proc p1
                  with Not_found ->
		    let t' = Terms.cst_for_type t.t_type in
		    if not (Terms.equal_terms t t') then 
                      begin
                        done_transfos := (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: (!done_transfos);
                        Settings.changed := true
                      end;
		    Terms.oproc_from_desc (Let(pat, t', rec_simplif above_proc p1, Terms.oproc_from_desc Yield))
		end
	    end
	  else
	    match remove_set with
	      All -> put_link true
	    | OneBinder b0 when b == b0 -> put_link true
	    | _ -> 
		match t.t_desc with
		  Var _ | ReplIndex _ when !Settings.expand_letxy -> 
	            (* Always expand assignments let x = x' and let x = constant, if possible,
                       but don't do a lot of work for that, so don't apply advises *)
		    put_link false
		| _ ->
		    Terms.oproc_from_desc (Let(pat, t, rec_simplif above_proc p1, Terms.oproc_from_desc Yield))
	end
      else
	Parsing_helper.internal_error "If, find, let, and new should not occur in expand_assign"

let several_def b =
  match b.def with
    [] | [_] -> false
  | _::_::_ -> true

let rec remove_assignments_term remove_set t =
  match t.t_desc with
    Var(b,l) ->
      Terms.build_term2 t (Var(b, List.map (remove_assignments_term remove_set) l))
  | ReplIndex i -> Terms.build_term2 t (ReplIndex i)
  | FunApp(f,l) ->
      Terms.build_term2 t (FunApp(f, List.map (remove_assignments_term remove_set) l))
  | TestE(t1,t2,t3) ->
      Terms.build_term2 t (TestE(remove_assignments_term remove_set t1,
		       remove_assignments_term remove_set t2,
		       remove_assignments_term remove_set t3))
  | FindE(l0, t3, find_info) ->
      Terms.build_term2 t (FindE(List.map (fun (bl, def_list, t1, t2) ->
	                 (bl, List.map (remove_assignments_br remove_set) def_list,
			  remove_assignments_term remove_set t1,
			  remove_assignments_term remove_set t2)) l0,
		       remove_assignments_term remove_set t3, find_info))
  | LetE(pat,t1,t2,topt) ->
      expand_assign_term t remove_set
	(remove_assignments_term remove_set)
	pat t1 t2 topt
  | ResE(b,t) ->
      if (!Settings.auto_sa_rename) && (several_def b) && (not (Terms.has_array_ref_q b)) then
	begin
	  let b' = Terms.new_binder b in
	  let t' = Terms.copy_term (Terms.Rename(List.map Terms.term_from_repl_index b.args_at_creation, b, b')) t in
	  Settings.changed := true;
	  done_sa_rename := (b,b') :: (!done_sa_rename);
	  Terms.build_term2 t' (ResE(b', remove_assignments_term remove_set t'))
	end
      else
	Terms.build_term2 t (ResE(b, remove_assignments_term remove_set t))
  | EventAbortE _ ->
      Parsing_helper.internal_error "Event should have been expanded"

and remove_assignments_br remove_set (b,l) =
  (b, List.map (remove_assignments_term remove_set) l)

let rec remove_assignments_rec remove_set p = 
  Terms.iproc_from_desc (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) -> 
      Par(remove_assignments_rec remove_set p1,
	  remove_assignments_rec remove_set p2)
  | Repl(b,p) ->
      Repl(b,remove_assignments_rec remove_set p)
  | Input((c,tl),pat,p) ->
      Input((c, List.map (remove_assignments_term remove_set) tl),pat, 
	    remove_assignments_reco remove_set p p))

and remove_assignments_reco remove_set above_proc p =
  match p.p_desc with
    Yield -> Terms.oproc_from_desc Yield
  | EventAbort f -> Terms.oproc_from_desc (EventAbort f)
  | Restr(b,p) ->
      if (!Settings.auto_sa_rename) && (several_def b) && (not (Terms.has_array_ref_q b)) then
	begin
	  let b' = Terms.new_binder b in
	  let p' = Terms.copy_oprocess (Terms.Rename(List.map Terms.term_from_repl_index b.args_at_creation, b, b')) p in
	  Settings.changed := true;
	  done_sa_rename := (b,b') :: (!done_sa_rename);
          (* Allow using b' for testing whether a variable is defined *) 
          b'.count_def <- 1;
          let above_proc' = Terms.oproc_from_desc (Restr(b',p)) in
	  Terms.oproc_from_desc (Restr(b',remove_assignments_reco remove_set above_proc' p'))
	end
      else
	Terms.oproc_from_desc (Restr(b,remove_assignments_reco remove_set above_proc p))
  | Test(t,p1,p2) ->
      Terms.oproc_from_desc (Test(remove_assignments_term remove_set t, 
	   remove_assignments_reco remove_set p1 p1,
	   remove_assignments_reco remove_set p2 p2))
  | Find(l0,p2,find_info) ->
      Terms.oproc_from_desc 
	(Find(List.map (fun (bl,def_list,t,p1) ->
	     (bl, def_list, 
	      remove_assignments_term remove_set t,
	      remove_assignments_reco remove_set p1 p1)) l0,
	   remove_assignments_reco remove_set p2 p2, find_info))
  | Output((c,tl),t2,p) ->
      Terms.oproc_from_desc 
	(Output((c, List.map (remove_assignments_term remove_set) tl), 
		remove_assignments_term remove_set t2,
		remove_assignments_rec remove_set p))
  | Let(pat, t, p1, p2) ->
      let rec_simplif = remove_assignments_reco remove_set in
      expand_assign p remove_set above_proc rec_simplif pat t p1 p2
  | EventP(t,p) ->
      Terms.oproc_from_desc 
	(EventP(remove_assignments_term remove_set t,
		remove_assignments_reco remove_set above_proc p))
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

(* - Main function for assignment removal *)

let remove_assignments remove_set p =
  Terms.build_def_process None p;
  if !Terms.current_bound_vars != [] then
    Parsing_helper.internal_error "bound vars should be cleaned up (transf1)";
  Terms.array_ref_process p;
  replacement_def_list := [];
  (* - First pass: put links; split assignments of tuples if possible *)
  let p' = remove_assignments_rec remove_set p in
  (* - Second pass: copy the process following the links or replacing just one variable.
       Be careful for array references: update the indexes properly  *)
  let p'' = Terms.copy_process (Terms.Links_Vars_Args(!replacement_def_list)) p' in
  Terms.cleanup();
  Terms.cleanup_array_ref();
  replacement_def_list := [];
  p''

let rec remove_assignments_repeat n remove_set p =
  let tmp_changed = !Settings.changed in
  Settings.changed := false;
  let p' = remove_assignments remove_set p in
  if n != 1 && !Settings.changed then
    remove_assignments_repeat (n-1) remove_set p'
  else
    begin
      Settings.changed := tmp_changed;
      p'
    end

let rec do_sa_rename = function
    [] -> []
  | ((b,b')::l) ->
      let lb = List.map snd (List.filter (fun (b1,b1') -> b1 == b) l) in
      let lr = do_sa_rename (List.filter (fun (b1,b1') -> b1 != b) l) in
      if Terms.is_restr b then
	(DSArenaming(b, b'::lb))::lr
      else
	(DSArenaming(b, b::b'::lb))::lr

let remove_assignments remove_set g =
  done_sa_rename := [];
  done_transfos := [];
  let r = 
    if remove_set == Minimal then
      remove_assignments_repeat (!Settings.max_iter_removeuselessassign) remove_set g.proc
    else
      remove_assignments remove_set g.proc
  in
  let sa_rename = !done_sa_rename in
  let transfos = !done_transfos in
  done_transfos := [];
  done_sa_rename := [];
  ({ proc = r; game_number = -1; current_queries = g.current_queries }, [], (do_sa_rename sa_rename) @ transfos)

