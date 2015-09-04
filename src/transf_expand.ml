(*************************************************************
 *                                                           *
 *       Cryptographic protocol verifier                     *
 *                                                           *
 *       Bruno Blanchet and David Cadé                       *
 *                                                           *
 *       Copyright (C) ENS, CNRS, INRIA, 2005-2015           *
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

(* Expand all if, let, and find in expressions, so that they occur only in 
   processes. 

expand_term returns either
  None: the term is unchanged
  Some(f,l): a function f that takes a list of processes (of the same
  length as l) as argument and a list of terms l. 

expand_term_list returns either
  None: the list of terms is unchanged
  Some(f,l): a function f that takes a list of processes (of the same
  length as l) as argument and a list of lists of terms l. 

After expansion, if/let/find/res may occur in terms only in conditions of find.
*)

(* Try to simplify a bit before expanding, to reduce the size of the expanded game *)

let current_pass_transfos = ref []

let simplify_term t = 
  if (Terms.check_no_ifletfindres t) && (not (Terms.is_true t || Terms.is_false t)) then
    begin
      try
	let facts = Facts.get_facts_at t.t_facts in
	let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) facts in
	let t' = Facts.simplify_term Facts.no_dependency_anal simp_facts t in
	(* When the obtained term is a complex term, using array accesses, I may
	   need to update defined conditions above the current program point.
	   To avoid the burden of doing that, I keep the result only when it is 
	   true or false. This is the only useful case for obtaining a smaller game in
	   expand, and the full simplification will be done later. *)
	if Terms.is_true t' || Terms.is_false t' then
	  begin
	    Settings.changed := true;
	    current_pass_transfos := (SReplaceTerm(t,t')) :: (!current_pass_transfos);
	    t'
	  end
	else
          (* The change is not really useful, don't do it *)
	  t
      with Contradiction ->
	(* The current program point is unreachable, I can return any term.
	   Returning false seems to be the best to get a smaller game.
	   Notice that simplify_term is called only for boolean terms
	   (conditions of if/find) so false is of the correct type. *)
	Settings.changed := true;
	let t' = Terms.make_false() in
	current_pass_transfos := (SReplaceTerm(t,t')) :: (!current_pass_transfos);
	t'
    end
  else
    t

let rec filter_find tfind = function
    [] -> []
  | ((bl, def_list, t, p) as findbranch)::r ->
      let r' = filter_find tfind r in
      let t' = simplify_term t in
      if Terms.is_false t' then 
	begin
	  current_pass_transfos := (SFindEBranchRemoved(tfind,findbranch)) :: (!current_pass_transfos);
	  r' 
	end
      else 
	(bl, def_list, t', p)::r'


let rec simplify_cterm t = 
  match t.t_desc with
    Var(b,l) -> Terms.build_term2 t (Var(b, List.map simplify_cterm l))
  | ReplIndex i -> Terms.build_term2 t (ReplIndex i)
  | FunApp(f,l) -> Terms.build_term2 t (FunApp(f, List.map simplify_cterm l))
  | TestE(t1,t2,t3) -> 
      (* Some trivial simplifications *)
      let t1' = simplify_term t1 in
      if Terms.is_true t1' then 
	begin
	  current_pass_transfos := (STestETrue t) :: (!current_pass_transfos);
	  simplify_cterm t2
	end
      else if Terms.is_false t1' then 
	begin
	  current_pass_transfos := (STestEFalse t) :: (!current_pass_transfos);
	  simplify_cterm t3
	end
      else
      Terms.build_term2 t (TestE(simplify_cterm t1', simplify_cterm t2, simplify_cterm t3))
  | FindE(l0,t3, find_info) -> 
      (* Remove useless branches if possible *)
      let l0 = filter_find t l0 in
      if l0 == [] then  
	begin
	  current_pass_transfos := (SFindERemoved(t)) :: (!current_pass_transfos);
	  simplify_cterm t3
	end
      else
      let l0' = List.map (fun (bl,def_list,t1,t2) ->
	let t1' = simplify_cterm t1 in
	let t2' = simplify_cterm t2 in
	(bl, def_list, t1', t2')) l0
      in
      let t3' = simplify_cterm t3 in
      Terms.build_term2 t (FindE(l0', t3', find_info))
  | LetE(pat, t1, t2, topt) ->
      let pat' = simplify_pat pat in
      let t1' = simplify_cterm t1 in
      let t2' = simplify_cterm t2 in
      let topt' = match topt with
	None -> None
      | Some t3 -> Some (simplify_cterm t3)
      in
      Terms.build_term2 t (LetE(pat', t1', t2', topt'))
  | ResE(b,t) ->
      Terms.build_term2 t (ResE(b, simplify_cterm t))
  | EventAbortE(f) ->
      Terms.build_term2 t (EventAbortE(f))

and simplify_pat = function
    PatVar b -> PatVar b
  | PatTuple (f,l) -> PatTuple(f,List.map simplify_pat l)
  | PatEqual t -> PatEqual(simplify_cterm t)

let rec simplify_process p = 
  Terms.iproc_from_desc 
      (match p.i_desc with
	Nil -> Nil
      | Par(p1,p2) -> 
	  let p1' = simplify_process p1 in
	  let p2' = simplify_process p2 in
	  Par(p1', p2')
      | Repl(b,p) -> Repl(b, simplify_process p)
      | Input((c,tl),pat,p) ->
	  let tl' = List.map simplify_cterm tl in
	  let pat' = simplify_pat pat in
	  let p' = simplify_oprocess p in
	  Input((c, tl'), pat', p'))

and simplify_oprocess p =
  Terms.oproc_from_desc 
      (match p.p_desc with
	Yield -> Yield
      |	EventAbort f -> EventAbort f
      | Restr(b,p) -> Restr(b, simplify_oprocess p)
      | Test(t,p1,p2) -> 
	  let t' = simplify_cterm t in
	  let p1' = simplify_oprocess p1 in
	  let p2' = simplify_oprocess p2 in
	  Test(t', p1', p2')
      | Find(l0, p2, find_info) -> 
	  let l0' = List.map (fun (bl, def_list, t, p1) -> 
	    let t' = simplify_cterm t in
	    let p1' = simplify_oprocess p1 in
	    (bl, def_list, t', p1')) l0
	  in
	  let p2' = simplify_oprocess p2 in
	  Find(l0', p2', find_info)
      | Let(pat,t,p1,p2) ->
	  let pat' = simplify_pat pat in
	  let t' = simplify_cterm t in
	  let p1' = simplify_oprocess p1 in
	  let p2' = simplify_oprocess p2 in	  
	  Let(pat', t', p1', p2')
      | Output((c,tl),t2,p) ->
	  let tl' = List.map simplify_cterm tl in
	  let t2' = simplify_cterm t2 in
	  let p' = simplify_process p in
	  Output((c, tl'), t2', p')
      | EventP(t,p) ->
	  let t' = simplify_cterm t in
	  let p' = simplify_oprocess p in
	  EventP(t', p')
      | Get(tbl,patl,topt,p1,p2) -> 
	  let patl' = List.map simplify_pat patl in
	  let topt' = 
	    match topt with 
	      Some t -> Some (simplify_cterm t) 
	    | None -> None
	  in
	  let p1' = simplify_oprocess p1 in
	  let p2' = simplify_oprocess p2 in	  
          Get(tbl,patl',topt',p1', p2')
      | Insert (tbl,tl,p) -> 
	  let tl' = List.map simplify_cterm tl in
	  let p' = simplify_oprocess p in
          Insert(tbl, tl', p'))

let simplify_process g =
  current_pass_transfos := [];
  Proba.reset [] g;
  Terms.build_def_process None g.proc;
  let p' = simplify_process g.proc in
  let simplif_transfos = 
    if (!current_pass_transfos) != [] then
      [DSimplify(!current_pass_transfos)]
    else
      []
  in
  current_pass_transfos := [];
  let proba = Proba.final_add_proba [] in
  (p', proba, simplif_transfos)

let check_no_ifletfind t =
  if not (Terms.check_no_ifletfindres t) then
    Parsing_helper.input_error "I cannot handle if, let, find, new inside the definition condition of a find. Sorry." t.t_loc

let check_no_ifletfind_br (_,l) =
  List.iter check_no_ifletfind l

(* Check if a term/pattern needs to be modified by expansion *)

let rec need_expand t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> List.exists need_expand l
  | ReplIndex _ -> false
  | _ -> true

let rec need_expand_pat = function
    PatVar _ -> false
  | PatTuple(_,l) -> List.exists need_expand_pat l
  | PatEqual t -> need_expand t
    
(* Expand term to term. Useful for conditions of find when they cannot be expanded to processes.
   Guarantees the invariant that if/let/find/res terms occur only in
   - conditions of find
   - at [ ] positions in TestE(t,[then],[else]), ResE(b,[...]), LetE(b,t,[in],[else]), 
     FindE((bl,def_list,[cond],[then]) list,[else])

   context = fun term -> C[term]
*)

let rec pseudo_expand_term t context = 
  match t.t_desc with
    Var(b,l) ->
      pseudo_expand_term_list l (fun li -> context (Terms.build_term t (Var(b,li))))
  | ReplIndex _ -> context t
  | FunApp(f,l) ->
      pseudo_expand_term_list l (fun li -> context (Terms.build_term t (FunApp(f,li))))
  | TestE(t1,t2,t3) ->
      let t2' = pseudo_expand_term t2 context in
      let t3' = pseudo_expand_term t3 context in
      pseudo_expand_term t1 (fun t1i ->
          (* Some trivial simplifications *)
        if Terms.is_true t1i then t2' else
        if Terms.is_false t1i then t3' else
	Terms.build_term t2' (TestE(t1i, t2', t3')))
  | LetE(pat, t1, t2, topt) ->
      let t2' = pseudo_expand_term t2 context in
      let topt' = match topt with
	None -> None
      | Some t3 -> Some (pseudo_expand_term t3 context)
      in
      pseudo_expand_term t1 (fun t1i ->
	pseudo_expand_pat pat (fun pati ->
	  Terms.build_term t2' (LetE(pati, t1i, t2', topt'))))
  | FindE(l0, t3, find_info) ->
      let rec expand_cond_find_list l context =
	match l with
	  [] -> context []
	| ((bl, def_list, t1, t2)::restl) ->
	    List.iter check_no_ifletfind_br def_list;
                  (* I move something outside a condition of
                     "find" only when bl and def_list are empty.  
                     I could be more precise, I would need to
                     check not only that what I move out does not
                     refer to the indices of "find", but also that it
                     is does not refer to the variables in the
                     "defined" condition---otherwise, some variable
                     accesses may not be defined after the
                     transformation *)
            if bl != [] || def_list != [] then
	      expand_cond_find_list restl (fun li ->
		context ((bl, def_list, pseudo_expand_term t1 (fun t -> t), t2)::li))
	    else
	      pseudo_expand_term t1 (fun t1i ->
		expand_cond_find_list restl (fun li -> context ((bl, def_list, t1i, t2)::li)))
      in

      let rec expand_res_find_list l context =
	match l with
	  [] -> []
	| ((bl, def_list, t1, t2)::restl) ->
	    (bl, def_list, t1, pseudo_expand_term t2 context) ::
	    (expand_res_find_list restl context)
      in 
      let expanded_res_l = expand_res_find_list l0 context in
      let expanded_res_t3 = pseudo_expand_term t3 context in
      expand_cond_find_list expanded_res_l (fun l1i ->
	Terms.build_term expanded_res_t3 (FindE(l1i, expanded_res_t3, find_info)))
  | ResE(b, t) ->
      let t' = pseudo_expand_term t context in
      Terms.build_term t' (ResE(b, t'))
  | EventAbortE _ ->
      Parsing_helper.internal_error "Events should not occur in conditions of find before expansion"

and pseudo_expand_term_list l context =
  match l with
    [] -> context []
  | (a::l) -> 
      pseudo_expand_term a (fun a' ->
	pseudo_expand_term_list l (fun l' -> context (a'::l')))

and pseudo_expand_pat pat context =
  match pat with
    PatVar b -> context (PatVar b)
  | PatTuple (ft,l) ->
      pseudo_expand_pat_list l (fun li -> context (PatTuple (ft,li)))
  | PatEqual t ->
      pseudo_expand_term t (fun ti -> context (PatEqual ti))

and pseudo_expand_pat_list l context =
  match l with
    [] -> context []
  | (a::l) -> 
      pseudo_expand_pat a (fun a' ->
	pseudo_expand_pat_list l (fun l' -> context (a'::l')))
	
and final_pseudo_expand t =
  pseudo_expand_term t (fun t -> t)

(* Expand term to process *)

let rec expand_term t context = 
  match t.t_desc with
    Var(b,l) ->
      expand_term_list l (fun li ->
	context (Terms.build_term t (Var(b,li))))
  | ReplIndex _ -> context t
  | FunApp(f,l) ->
      expand_term_list l (fun li ->
	context (Terms.build_term t (FunApp(f,li))))
  | TestE(t1,t2,t3) ->
      let t2' = expand_term t2 context in
      let t3' = expand_term t3 context in
      expand_term t1 (fun t1i ->
          (* Some trivial simplifications *)
        if Terms.is_true t1i then t2' else
        if Terms.is_false t1i then t3' else
	Terms.oproc_from_desc (Test(t1i,  t2', t3')))

  | LetE(pat, t1, t2, topt) ->
      let t2' = expand_term t2 context in
      let p3 = match topt with
	None -> Terms.oproc_from_desc Yield
      | Some t3 -> expand_term t3 context
      in
      expand_term t1 (fun t1i ->
	expand_pat pat (fun pati ->
	  Terms.oproc_from_desc (Let(pati, t1i, t2', p3))))
  | FindE(l0, t3, find_info) ->
      let rec expand_cond_find_list l context =
	match l with
	  [] -> context []
	| ((bl, def_list, t1, t2)::restl) ->
	    List.iter check_no_ifletfind_br def_list;
                  (* I move something outside a condition of
                     "find" only when bl and def_list are empty.  
                     I could be more precise, I would need to
                     check not only that what I move out does not
                     refer to the indices of "find", but also that it
                     is does not refer to the variables in the
                     "defined" condition---otherwise, some variable
                     accesses may not be defined after the
                     transformation *)
            if bl != [] || def_list != [] then
	      expand_cond_find_list restl (fun li ->
		context ((bl, def_list, final_pseudo_expand t1, t2)::li))
	    else
	      expand_term t1 (fun t1i ->
		 expand_cond_find_list restl (fun li -> context ((bl, def_list, t1i, t2)::li)))
      in

      let rec expand_res_find_list l context =
	match l with
	  [] -> []
	| ((bl, def_list, t1, t2)::restl) ->
	    (bl, def_list, t1, expand_term t2 context) ::
	    (expand_res_find_list restl context)
      in 
      let expanded_res_l = expand_res_find_list l0 context in
      let t3' = expand_term t3 context in
      expand_cond_find_list expanded_res_l (fun l1i ->
	Terms.oproc_from_desc (Find(l1i, t3', find_info)))
  | ResE(b, t) ->
      Terms.oproc_from_desc (Restr(b, expand_term t context))
  | EventAbortE(f) ->
      (* The event is expanded to a process that stops just after the event.
	 Events in terms are used only in the RHS of equivalences, and 
	 one includes their probability of execution in the probability of
	 breaking the protocol. *)
      Terms.oproc_from_desc (EventAbort f)

and expand_term_list l context =
  match l with
    [] -> context []
  | (a::l) -> 
      expand_term a (fun a' ->
	expand_term_list l (fun l' -> context (a'::l')))

and expand_pat pat context =
  match pat with
    PatVar b -> context (PatVar b)
  | PatTuple (ft,l) ->
      expand_pat_list l (fun li -> context (PatTuple (ft,li)))
  | PatEqual t ->
      expand_term t (fun ti -> context (PatEqual ti))

and expand_pat_list l context =
  match l with
    [] -> context []
  | (a::l) -> 
      expand_pat a (fun a' ->
	expand_pat_list l (fun l' -> context (a'::l')))


(* Expand process to process *)

let rec expand_process cur_array p = 
  match p.i_desc with
    Nil -> Terms.iproc_from_desc Nil
  | Par(p1,p2) ->
      Terms.iproc_from_desc  (Par(expand_process cur_array p1,
				  expand_process cur_array p2))
  | Repl(b,p) ->
      Terms.iproc_from_desc (Repl(b, expand_process (b::cur_array) p))
  | Input((c,tl),pat,p) ->
      List.iter check_no_ifletfind tl;
      if need_expand_pat pat then
	begin
	  Settings.changed := true;
	  let b = Terms.create_binder "patv" (Terms.new_vname()) 
	      Settings.t_bitstring cur_array
	  in
	  let p' = expand_oprocess cur_array p in
	  Terms.iproc_from_desc (Input((c,tl),PatVar b, 
	      expand_pat pat (fun pati -> Terms.oproc_from_desc 
                  (Let(pati, Terms.term_from_binder b,
		       p', Terms.oproc_from_desc Yield)))))
	end
      else
        Terms.iproc_from_desc (Input((c,tl),pat, expand_oprocess cur_array p))

and expand_oprocess cur_array p =
  match p.p_desc with 
    Yield -> Terms.oproc_from_desc Yield
  | EventAbort f -> Terms.oproc_from_desc (EventAbort f)
  | Restr(b,p) -> Terms.oproc_from_desc (Restr(b, expand_oprocess cur_array p))
  | Test(t,p1,p2) ->
      let p1' = expand_oprocess cur_array p1 in
      let p2' = expand_oprocess cur_array p2 in
      if need_expand t then
	begin
	  Settings.changed := true;
	  expand_term t (fun ti ->
            (* Some trivial simplifications *)
            if Terms.is_true ti then p1' else
            if Terms.is_false ti then p2' else
	    Terms.oproc_from_desc (Test(ti,p1',p2')))
	end
      else
	Terms.oproc_from_desc (Test(t,p1',p2'))
  | Find(l0, p2, find_info) ->
      let l0' = List.map (fun (bl, def_list, t, p1) ->
	(bl, def_list, t, expand_oprocess cur_array p1)) l0
      in
      let rec expand_find_list next_f = function
	  [] -> next_f []
	| ((bl, def_list, t, p1)::rest_l) ->
	    List.iter check_no_ifletfind_br def_list;
	    if need_expand t then
	      begin
		Settings.changed := true;
		if bl != [] || def_list != [] then
		  expand_find_list (fun rest_l' ->
		    next_f ((bl, def_list, final_pseudo_expand t, p1)::rest_l')) rest_l
		else
		  expand_term t (fun ti -> expand_find_list (fun rest_l' ->
		    next_f ((bl, def_list, ti, p1)::rest_l')) rest_l)
	      end
	    else
	      expand_find_list (fun rest_l' ->
		next_f ((bl, def_list, t, p1)::rest_l')) rest_l
      in
      let p2' = expand_oprocess cur_array p2 in
      expand_find_list (fun l0'' -> Terms.oproc_from_desc (Find(l0'', p2', find_info))) l0'
  | Output((c,tl),t2,p) ->
      let p' = expand_process cur_array p in
      if (List.exists need_expand tl) || (need_expand t2) then
	begin
	  Settings.changed := true;
	  expand_term_list tl (fun tli ->
	    expand_term t2 (fun t2i ->
	      Terms.oproc_from_desc (Output((c,tli),t2i,p'))))
	end
      else
	Terms.oproc_from_desc (Output((c,tl),t2,p'))
  | Let(pat,t,p1,p2) ->
      let p1' = expand_oprocess cur_array p1 in
      let p2' = expand_oprocess cur_array p2 in
      if (need_expand_pat pat) || (need_expand t) then
	begin
	  Settings.changed := true;
	  expand_term t (fun ti ->
	    expand_pat pat (fun pati ->
	      Terms.oproc_from_desc (Let(pati,ti,p1',p2'))))
	end
      else
	Terms.oproc_from_desc (Let(pat, t, p1', p2'))
  | EventP(t,p) ->
      let p' = expand_oprocess cur_array p in
      if need_expand t then
	begin
	  Settings.changed := true;
	  expand_term t (fun ti -> Terms.oproc_from_desc (EventP(ti, p')))
	end
      else
	Terms.oproc_from_desc (EventP(t, p'))
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

(* Main function for expansion of if and find
   Call auto_sa_rename after expand_process, so that facts associated with 
   nodes are emptied, and variables defined in
   conditions of find have a single definition. 
   Expansion is called only when there is no advice pending, so we can simply 
   ignore the list of done SArenamings.
*)

let expand_process g =
  let (g', proba0, ins0) = Transf_auto_sa_rename.auto_sa_rename g in
  let tmp_changed = !Settings.changed in
  let (p', proba, simplif_transfos) = simplify_process g' in
  let p'' = expand_process [] p' in
  if !Settings.changed then 
    let (g'', proba', ins) = Transf_auto_sa_rename.auto_sa_rename { proc = p''; game_number = -1; current_queries = g'.current_queries } in
    (g'', proba' @ proba @ proba0, ins @ (DExpandIfFind :: simplif_transfos) @ ins0)
  else
    begin
      Settings.changed := tmp_changed;
      (g', proba0, ins0)
    end
    
