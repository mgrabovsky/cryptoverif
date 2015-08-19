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

(* When variable x is assigned at several places, 
   rename variable x into x1, ..., xn and duplicate code if necessary 

This transformation assumes that LetE/FindE/TestE/ResE occur only in 
conditions of find, which is guaranteed after expansion.
(In fact, Terms.copy_process and sa_process support them in all terms, 
although that's not necessary.
ren_out_process and Terms.build_compatible_defs support 
LetE/FindE/TestE/ResE only in conditions of find.
Otherwise, ren_out_process should call ren_out_find_cond for each term,
and not only for find conditions.)
It also assumes that variables defined in conditions of find
have no array references and do not occur in queries.
*)

(* - First pass: look for assignments to x, give a new name to each of them,
   and rename the in-scope references to x with current session identifiers *)
   
let image_name_list = ref []

(* NOTE: when TestE/LetE/FindE/ResE are forbidden, sa_term is the identity *)
let rec sa_term b0 t =
  Terms.build_term t 
     (match t.t_desc with
	Var(b,l) ->
          Var(b, List.map (sa_term b0) l)
      | ReplIndex(b) -> ReplIndex(b)
      | FunApp(f,l) ->
          FunApp(f, List.map (sa_term b0) l)
      | TestE(t1,t2,t3) ->
          TestE(sa_term b0 t1,
		sa_term b0 t2,
		sa_term b0 t3)
      | FindE(l0,t3,find_info) ->
	  let l0' = List.map (fun (bl, def_list, t1, t2) ->
            if List.exists (fun (b,_) -> b == b0) bl then
              let b0' = Terms.new_binder b0 in
              image_name_list := b0' :: (!image_name_list);
              (List.map (fun (b,b') -> ((if b == b0 then b0' else b), b')) bl,
               def_list,
               (* b0 cannot be defined in t1, because the array arguments
                  of b0 are the current indices at the find, which are fewer
                  than the current indices in t1, since the latter include the
                  non-empty list bl *)
               t1,
               Terms.copy_term (Terms.Rename(List.map Terms.term_from_repl_index b0.args_at_creation, b0, b0')) t2)
            else
	      (* def_list does not contain if/let/find/res so
		 no change in it *)
              (bl, def_list, 
               sa_term b0 t1,
               sa_term b0 t2)) l0
	  in
	  FindE(l0', sa_term b0 t3, find_info)
      |	LetE(pat, t1, t2, topt) ->
	  let target_name = ref b0 in
	  let pat' = sa_pat b0 target_name pat in
	  if !target_name == b0 then
	  (* b0 not defined in pat *)
	    LetE(pat', t1, 
		sa_term b0 t2, 
		match topt with
		  Some t3 -> Some (sa_term b0 t3)
		| None -> None)
	  else
	    (* b0 defined in pat and renamed to !target_name *)
	    LetE(pat', t1, 
		Terms.copy_term (Terms.Rename(List.map Terms.term_from_repl_index b0.args_at_creation, b0, !target_name)) t2, 
		match topt with
		  Some t3 -> Some (sa_term b0 t3)
		| None -> None)
      |	ResE(b,t) ->
	  if b == b0 then
	    let b0' = Terms.new_binder b0 in
	    image_name_list := b0' :: (!image_name_list);
	    ResE(b0', Terms.copy_term (Terms.Rename(List.map Terms.term_from_repl_index b0.args_at_creation, b0, b0')) t)
	  else
	    ResE(b, sa_term b0 t)
      |	EventAbortE _ ->
          Parsing_helper.internal_error "Event should have been expanded")

and sa_pat b0 target_name = function
    PatVar b -> 
      if b == b0 then
	let b0' = Terms.new_binder b0 in
	image_name_list := b0' :: (!image_name_list);
	if (!target_name) != b0 then 
	  Parsing_helper.internal_error "target name already assigned in sa_pat";
	target_name := b0';
	PatVar b0'
      else
	PatVar b
  | PatTuple (f,l) -> PatTuple (f,List.map (sa_pat b0 target_name) l)
  | PatEqual t -> PatEqual (sa_term b0 t)

let rec sa_process b0 p = 
  Terms.iproc_from_desc (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) -> Par(sa_process b0 p1,
		      sa_process b0 p2)
  | Repl(b,p) ->
      Repl(b, sa_process b0 p)
  | Input((c,tl),pat,p) ->
      let target_name = ref b0 in
      let pat' = sa_pat b0 target_name pat in
      if !target_name == b0 then
	(* b0 not defined in pat *)
	Input((c,List.map (sa_term b0) tl), pat', 
	      sa_oprocess b0 p)
      else
	(* b0 defined in pat and renamed to !target_name *)
	Input((c,List.map (sa_term b0) tl), pat', 
	      Terms.copy_oprocess (Terms.Rename(List.map Terms.term_from_repl_index b0.args_at_creation, b0, !target_name)) p))

and sa_oprocess b0 p = 
  Terms.oproc_from_desc (
  match p.p_desc with
    Yield -> Yield
  | EventAbort f -> EventAbort f
  | Restr(b,p) ->
      if b == b0 then
	let b0' = Terms.new_binder b0 in
	image_name_list := b0' :: (!image_name_list);
	Restr(b0', Terms.copy_oprocess (Terms.Rename(List.map Terms.term_from_repl_index b0.args_at_creation, b0, b0')) p)
      else
	Restr(b, sa_oprocess b0 p)
  | Test(t,p1,p2) ->
      Test(sa_term b0 t, 
	   sa_oprocess b0 p1,
	   sa_oprocess b0 p2)
  | Find(l0, p2, find_info) -> 
      let l0' = List.map (fun (bl, def_list, t, p1) ->
        if List.exists (fun (b,_) -> b == b0) bl then
	  let b0' = Terms.new_binder b0 in
	  image_name_list := b0' :: (!image_name_list);
	  (List.map (fun (b,b') -> ((if b == b0 then b0' else b), b')) bl, 
	   def_list,
               (* b0 cannot be defined in t, because the array arguments
                  of b0 are the current indices at the find, which are fewer
                  than the current indices in t, since the latter include the
                  non-empty list bl *)
	   t,
	   Terms.copy_oprocess (Terms.Rename(List.map Terms.term_from_repl_index b0.args_at_creation, b0, b0')) p1)
	else
	  (* def_list does not contain if/let/find/res so
	     no change in it *)
	  (bl, def_list, 
	   sa_term b0 t,
	   sa_oprocess b0 p1)) l0
      in
      Find(l0', sa_oprocess b0 p2, find_info)
  | Output((c,tl),t2,p) ->
      Output((c, List.map (sa_term b0) tl), 
	     sa_term b0 t2,
	     sa_process b0 p)
  | Let(pat,t,p1,p2) ->
      let target_name = ref b0 in
      let pat' = sa_pat b0 target_name pat in
      if !target_name == b0 then
	(* b0 not defined in pat *)
	Let(pat', t, 
	    sa_oprocess b0 p1, 
	    sa_oprocess b0 p2)
      else
	(* b0 defined in pat and renamed to !target_name *)
	Let(pat', t, 
	    Terms.copy_oprocess (Terms.Rename(List.map Terms.term_from_repl_index b0.args_at_creation, b0, !target_name)) p1, 
	    sa_oprocess b0 p2)
  | EventP(t,p) ->
      EventP(sa_term b0 t,
	     sa_oprocess b0 p)
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  )
(* - Second pass: empty b.def 
	          compute new value of b.def
     See terms.ml *)
      
(* - Third pass: rename the out-scope array references to x
   A find ... suchthat defined(M1...Mn) should be split if 
   x[...] is a subterm of M1...Mn 
      x[...] becomes x1[...], ..., xn[...] in the different cases

   If due to other defined conditions, only some of the xi can be
   defined then consider only these xi cases: collect all "defined"
   conditions up to the current point. On the other hand, collect the
   variables defined in the same branch as xi. The case xi needs to be
   considered only when all "defined" conditions up to the current
   point that have session identifiers prefix or suffix of those of xi
   are variables defined in the same branch as xi.  Use
   compatible_defs to test whether two variables are in the same
   branch.  
*)

let proba_accu = ref []

let add_proba_sarename bl find_info =
  (* If find_info = Unique or bl = [], there is a single possible
     choice in the current branch, so SArename will not change the
     order of the elements in the list of successful find choices.
     If find_info != Unique and bl != [], SArename may reorder the
     elements in the list of successful find choices. If the
     distribution is not exactly uniform, this may lead to a change
     of probability EpsFind of these choices, for each execution
     of the find. *)
  if find_info != Unique then
    begin
      match bl with
	[] -> ()
      |	((b,_)::_) ->
	  if (!Settings.ignore_small_times) <= 0 then
	    proba_accu := 
	       (SetProba (Polynom.p_mul ((Proba.card_index b), EpsFind)))
	       :: (!proba_accu)
    end

let rec implies_def_subterm b0 accu (b,l) =
  if (b == b0) && 
    (* Do not add duplicates in accu *)
    (not (List.exists (fun l' -> List.for_all2 Terms.equal_terms l l') (!accu))) then
    accu := l :: (!accu);
  List.iter (implies_def_term b0 accu) l

and implies_def_term b0 accu t =
  match t.t_desc with
    Var(b,l) -> implies_def_subterm b0 accu (b,l)
  | ReplIndex _ -> ()
  | FunApp(f,l) -> List.iter (implies_def_term b0 accu) l
  | _ -> Parsing_helper.internal_error "if/let/find forbidden in defined conditions of find"
    
let implies_def b0 def_list =
  let accu = ref [] in
  List.iter (implies_def_subterm b0 accu) def_list;
  !accu

let rec rename_find p1rename b0 image_list args accu ((bl,def_list,t,p1) as p) =
  match image_list with
    [] -> accu
  | (b::l) ->
      let accu' = 
	if List.for_all (function (b', args') -> (b' == b0) || (Terms.is_compatible (b,args) (b',args'))) def_list then
	  let def_list' = List.map (Terms.copy_binder (Terms.Rename(args, b0, b))) def_list in
	  let def_list'' = 
	    if not (List.exists (fun (b',l') -> (b' == b0) && (List.for_all2 Terms.equal_terms l' args)) def_list) then
	      (b,args)::def_list'
	    else
	      def_list'
	  in
          (* In p1, args uses the variables in bl, instead of the replication indices used in def_list/t *)
          let args' = List.map (Terms.subst (List.map snd bl) (List.map (fun (b,_) -> Terms.term_from_binder b) bl)) args in
	  (bl, def_list'',
	   Terms.copy_term (Terms.Rename(args, b0, b)) t, 
	   p1rename (Terms.Rename(args', b0, b)) p1) :: accu
	else
          accu
      in
      rename_find p1rename b0 l args accu' p

let rec rename_finds p1rename b0 image_list args_list accu p =
  match args_list with
    [] ->  accu 
  | (args::args_list) ->
      rename_finds p1rename b0 image_list args_list (rename_find p1rename b0 image_list args accu p) p

let rec ren_out_find_cond b0 t = 
  Terms.build_term t (
  match t.t_desc with
    Var(b,l) -> Var(b, List.map (ren_out_find_cond b0) l)
  | ReplIndex(b) -> ReplIndex(b)
  | FunApp(f,l) -> FunApp(f, List.map (ren_out_find_cond b0) l)
  | ResE(b,p) -> ResE(b, ren_out_find_cond b0 p)
  | TestE(t,p1,p2) -> 
      TestE(t,
	   ren_out_find_cond b0 p1,
	   ren_out_find_cond b0 p2)
  | FindE(l0, p2, find_info) ->
      let rec ren_out_list = function
	  [] -> []
	| (bl,def_list, t, p1)::l1 ->
	    let l1' = ren_out_list l1 in
	    let p1' = ren_out_find_cond b0 p1 in
            let t' = ren_out_find_cond b0 t in
	    let to_rename = implies_def b0 def_list in
            (* renamings of b0 *)	
	    if to_rename = [] then
	      (bl, def_list, t', p1')::l1'
	    else
	      begin
		add_proba_sarename bl find_info;
		rename_finds Terms.copy_term b0 (!image_name_list) to_rename l1' (bl, def_list, t', p1')
	      end
      in
      FindE(ren_out_list l0, ren_out_find_cond b0 p2, find_info)
  | LetE(pat,t,p1,topt) ->
      begin
      LetE(pat, t, ren_out_find_cond b0 p1,
	  match topt with
            None -> None
          | Some p2 -> Some (ren_out_find_cond b0 p2))
      end
  | EventAbortE _ ->
      Parsing_helper.internal_error "Event should have been expanded")


let rec ren_out_process b0 p = 
  Terms.iproc_from_desc (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) -> Par(ren_out_process b0 p1,
		      ren_out_process b0 p2)
  | Repl(b,p) -> Repl(b, ren_out_process b0 p)
  | Input((c,tl),pat,p) ->
      Input((c, tl), pat, ren_out_oprocess b0 p))

and ren_out_oprocess b0 p = 
  Terms.oproc_from_desc (
  match p.p_desc with
    Yield -> Yield
  | EventAbort f -> EventAbort f
  | Restr(b,p) -> Restr(b, ren_out_oprocess b0 p)
  | Test(t,p1,p2) -> 
      Test(t,
	   ren_out_oprocess b0 p1,
	   ren_out_oprocess b0 p2)
  | Find(l0, p2, find_info) ->
      let rec ren_out_list = function
	  [] -> []
	| (bl,def_list, t, p1)::l1 ->
	    let l1' = ren_out_list l1 in
	    let p1' = ren_out_oprocess b0 p1 in
            let t' = ren_out_find_cond b0 t in
	    let to_rename = implies_def b0 def_list in
            (* renamings of b0 *)	
	    if to_rename = [] then
	      (bl, def_list, t', p1')::l1'
	    else
	      begin
		add_proba_sarename bl find_info;
		rename_finds Terms.copy_oprocess b0 (!image_name_list) to_rename l1' (bl, def_list, t', p1')
	      end
      in
      Find(ren_out_list l0, ren_out_oprocess b0 p2, find_info)
  | Output((c,tl),t2,p) ->
      Output((c, tl),t2,ren_out_process b0 p)
  | Let(pat,t,p1,p2) ->
      Let(pat, t, ren_out_oprocess b0 p1,
	  ren_out_oprocess b0 p2)
  | EventP(t,p) ->
      EventP(t, ren_out_oprocess b0 p)
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  )

(* Main function for variable renaming into sa *)

let sa_rename b0 g =
  let p = g.proc in
  (* cannot rename if b0 occurs in queries! 
     TO DO in fact, I could replace b0 = M with b' = M; b0 = b',
     replace all references to b0 with b', and apply sa_rename on b' *)
  if Settings.occurs_in_queries b0 then (g, [], []) else
  begin
    image_name_list := [];
    proba_accu := [];
    let p' = sa_process b0 p in
    if List.length (!image_name_list) >= 2 then
      begin
	Settings.changed := true;
	Terms.build_def_process None p';
	Terms.build_compatible_defs p';
	let p'' = ren_out_process b0 p' in
	let new_names = !image_name_list in
	let probaSArename = !proba_accu in
	image_name_list := [];
	proba_accu := [];
	Terms.empty_comp_process p';
	let (g', proba, renames) = Transf_auto_sa_rename.auto_sa_rename { proc = p''; game_number = -1; current_queries = g.current_queries } in      
	(g', proba @ probaSArename, renames @ [DSArenaming(b0,new_names)])
      end
    else
      begin
	image_name_list := [];
	proba_accu := [];
	(g, [], [])
      end
  end

