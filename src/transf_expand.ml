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


let rec cross_product l1 = function
    [] -> []
  | (a::l) -> (List.map (fun l1i -> (l1i,a)) l1) @ (cross_product l1 l)

let rec split_every n = function
    [] -> []
  | l ->
      let (l1,l2) = Terms.split n l in
      l1 :: (split_every n l2)

let check_no_ifletfind t =
  if not (Terms.check_no_ifletfindres t) then
    Parsing_helper.input_error "I cannot handle if, let, find, new inside the definition condition of a find. Sorry." t.t_loc

let check_no_ifletfind_br (_,l) =
  List.iter check_no_ifletfind l

let pairing_expand a l aex lex =
  match aex, lex with
    None, None -> None
  | Some(fa,la),None -> Some(fa, List.map (fun lai -> (lai,l)) la)
  | None,Some(fl,ll) -> Some(fl, List.map (fun lli -> (a,lli)) ll)
  | Some(fa,la),Some(fl,ll) ->
      let len = List.length la in
      Some((fun l -> let l' = split_every len l in
                     fl (List.map fa l')), cross_product la ll)

let extract_elem = function
    [p] -> p
  | _ -> Parsing_helper.internal_error "list with single element expected"

let always_some t = function
    None -> (extract_elem, [t])
  | Some(f,l) -> (f,l)

(* Expand term to term. Useful for conditions of find when they cannot be expanded to processes.
   Guarantees the invariant that if/let/find/res terms occur only in
   - conditions of find
   - at [ ] positions in TestE(t,[then],[else]), ResE(b,[...]), LetE(b,t,[in],[else]), 
     FindE((bl,def_list,[cond],[then]) list,[else])
*)

let rec pseudo_expand_term t = 
  match t.t_desc with
    Var(b,l) ->
      begin
        match pseudo_expand_term_list l with
          None -> None
        | Some(f,l') ->
            Some(f, List.map (fun li -> Terms.build_term t (Var(b,li))) l')
      end 
  | ReplIndex _ -> None 
  | FunApp(f,l) ->
      begin
        match pseudo_expand_term_list l with
          None -> None
        | Some(f',l') -> Some(f', List.map (fun li -> Terms.build_term t (FunApp(f,li))) l')
      end
  | TestE(t1,t2,t3) ->
      (* I always expand this test *)
      let (f2, l2) = always_some t2 (pseudo_expand_term t2) in
      let (f3, l3) = always_some t3 (pseudo_expand_term t3) in
      let (f1, l1) = always_some t1 (pseudo_expand_term t1) in
      let len2 = List.length l2 in
      Some((fun l -> 
	let (l2part, l3part) = Terms.split len2 l in
	f1 (List.map (fun t1i -> 
          (* Some trivial simplifications *)
          if Terms.is_true t1i then f2 l2part else
          if Terms.is_false t1i then f3 l3part else
          let t2' = f2 l2part in Terms.build_term t2' (TestE(t1i, t2', f3 l3part))) l1)), l2 @ l3)
  | LetE(pat, t1, t2, topt) ->
      let (fpat,lpat) = always_some pat (pseudo_expand_pat pat) in
      let (f1,l1) = always_some t1 (pseudo_expand_term t1) in
      let (f2,l2) = always_some t2 (pseudo_expand_term t2) in
      begin
	match topt with
	  None ->
	    Some ((fun l -> 
	      f1 (List.map (fun t1i -> 
		fpat (List.map (fun pati ->
                  let t2' = f2 l in
		  Terms.build_term t2' (LetE(pati, t1i, t2', None))) lpat)) l1)), l2)
	| Some t3 ->
	    let (f3,l3) = always_some t3 (pseudo_expand_term t3) in
	    let len2 = List.length l2 in
	    Some ((fun l -> 
	      let (l2part, l3part) = Terms.split len2 l in
	      f1 (List.map (fun t1i -> 
		fpat (List.map (fun pati ->
                  let t2' = f2 l2part in
		  Terms.build_term t2' (LetE(pati, t1i, t2', Some (f3 l3part)))) lpat)) l1)), l2 @ l3)
      end
  | FindE(l0, t3, find_info) ->
      let rec expand_cond_find_list = function
	  [] -> None
	| ((bl, def_list, t1, t2)::restl) ->
	    List.iter check_no_ifletfind_br def_list;
	    let rest_lex = expand_cond_find_list restl in
	    let ex1 = pseudo_expand_term t1 in
	    let ex1 = 
	      match ex1 with
		None -> None
	      | Some(f,l) ->
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
                    Some(extract_elem, [f l])
                  else 
                    ex1
		  (*let tf = f (List.map (fun t -> 
		    let b = Terms.create_binder "tmp"
			      (Terms.new_vname()) t.t_type []
		    in 
		    Terms.build_term t (Var(b,[]))) l) 
		  in
		  if List.exists (fun b -> Terms.refers_to b tf) bl || [tf refers to variables in def_list] then
		    Some(extract_elem, [f l]) (* We cannot move the condition of the find outside, because it refers to variables defined in the find. In this case, we leave the term without expanding it. *)
                  else
                    ex1*)
            in
	    match pairing_expand t1 restl ex1 rest_lex with
	      None -> None
	    | Some(f,l') -> Some(f, List.map (fun (a,l'') -> (bl, def_list, a, t2)::l'') l')
      in

      let rec expand_res_find_list = function
	  [] -> ((fun l -> []), [])
	| ((bl, def_list, t1, t2)::restl) ->
	    let (frestl, lrestl) = expand_res_find_list restl in
	    let (f2, l2) = always_some t2 (pseudo_expand_term t2) in
	    let len2 = List.length l2 in
	    ((fun l -> 
	      let (l2part, l3part) = Terms.split len2 l in
	      (bl, def_list, t1, f2 l2part) :: (frestl l3part)),
	     l2 @ lrestl)
      in 
      let (f2, l2) = expand_res_find_list l0 in
      let (f3, l3) = always_some t3 (pseudo_expand_term t3) in
      let len3 = List.length l3 in
      Some((fun l -> 
	let (l3part, l2part) = Terms.split len3 l in
	let expanded_res_l = f2 l2part in
	let expanded_res_t3 = f3 l3part in
	let (f1, l1) = always_some expanded_res_l (expand_cond_find_list expanded_res_l) in
        f1 (List.map (fun l1i -> Terms.build_term expanded_res_t3 (FindE(l1i, expanded_res_t3, find_info))) l1)), l3 @ l2)
  | ResE(b, t) ->
      let (f,l) = always_some t (pseudo_expand_term t) in
      Some((fun l -> let t' = f l in Terms.build_term t' (ResE(b, t'))), l)
  | EventAbortE _ ->
      Parsing_helper.internal_error "Events should not occur in conditions of find before expansion"

and pseudo_expand_term_list = function
  [] -> None
| (a::l) -> 
    let aex = pseudo_expand_term a in
    let lex = pseudo_expand_term_list l in
    match pairing_expand a l aex lex with
      None -> None
    | Some(f,l') -> Some(f, List.map (fun (a,l'') -> a::l'') l')

and pseudo_expand_pat = function
    PatVar b -> None
  | PatTuple (ft,l) -> 
      begin
	match pseudo_expand_pat_list l with
	  None -> None
	| Some(f,l') -> Some(f, List.map (fun li -> PatTuple (ft,li)) l')
      end 
  | PatEqual t -> 
      begin
	match pseudo_expand_term t with
	  None -> None
	| Some(f,l) -> Some (f, List.map (fun ti -> PatEqual ti) l)
      end

and pseudo_expand_pat_list = function
  [] -> None
| (a::l) -> 
    let aex = pseudo_expand_pat a in
    let lex = pseudo_expand_pat_list l in
    match pairing_expand a l aex lex with
      None -> None
    | Some(f,l') -> Some(f, List.map (fun (a,l'') -> a::l'') l')

and final_pseudo_expand t =
  match pseudo_expand_term t with
    None -> t
  | Some(f,l) -> f l

(* Expand term to process *)

let rec expand_term t = 
  match t.t_desc with
    Var(b,l) ->
      begin
        match expand_term_list l with
          None -> None
        | Some(f,l') ->
            Some(f, List.map (fun li -> Terms.build_term t (Var(b,li))) l')
      end 
  | ReplIndex _ -> None 
  | FunApp(f,l) ->
      begin
        match expand_term_list l with
          None -> None
        | Some(f',l') -> Some(f', List.map (fun li -> Terms.build_term t (FunApp(f,li))) l')
      end
  | TestE(t1,t2,t3) ->
      (* I always expand this test *)
      let (f2, l2) = always_some t2 (expand_term t2) in
      let (f3, l3) = always_some t3 (expand_term t3) in
      let (f1, l1) = always_some t1 (expand_term t1) in
      let len2 = List.length l2 in
      Some((fun l -> 
	let (l2part, l3part) = Terms.split len2 l in
	f1 (List.map (fun t1i -> 
          (* Some trivial simplifications *)
          if Terms.is_true t1i then f2 l2part else
          if Terms.is_false t1i then f3 l3part else
          Terms.oproc_from_desc (Test(t1i, f2 l2part, f3 l3part))) l1)), l2 @ l3)
  | LetE(pat, t1, t2, topt) ->
      let (fpat,lpat) = always_some pat (expand_pat pat) in
      let (f1,l1) = always_some t1 (expand_term t1) in
      let (f2,l2) = always_some t2 (expand_term t2) in
      begin
	match topt with
	  None ->
	    Some ((fun l -> 
	      f1 (List.map (fun t1i -> 
		fpat (List.map (fun pati ->
		  Terms.oproc_from_desc (Let(pati, t1i, f2 l, Terms.oproc_from_desc Yield))) lpat)) l1)), l2)
	| Some t3 ->
	    let (f3,l3) = always_some t3 (expand_term t3) in
	    let len2 = List.length l2 in
	    Some ((fun l -> 
	      let (l2part, l3part) = Terms.split len2 l in
	      f1 (List.map (fun t1i -> 
		fpat (List.map (fun pati ->
		  Terms.oproc_from_desc (Let(pati, t1i, f2 l2part, f3 l3part))) lpat)) l1)), l2 @ l3)
      end
  | FindE(l0, t3, find_info) ->
      let rec expand_cond_find_list = function
	  [] -> None
	| ((bl, def_list, t1, t2)::restl) ->
	    List.iter check_no_ifletfind_br def_list;
	    let rest_lex = expand_cond_find_list restl in
	    let ex1 = expand_term t1 in
	    let ex1 = 
	      match ex1 with
		None -> None
	      | Some(f,l) ->
                  if bl != [] || def_list != [] then
                    Some(extract_elem, [final_pseudo_expand t1])
                  else
                    ex1
		  (*let fNil = f (List.map (fun _ -> Terms.oproc_from_desc Yield) l) in
		  if List.exists (fun b -> Terms.refers_to_oprocess b fNil) bl || [fNil refers to variables in def_list] | [fNil contains new and bl != [] ] then
		    Some (extract_elem, [final_pseudo_expand t1]) (* We cannot move the condition of the find outside, because it refers to variables defined in the find. In this case, we leave the term with if/let/find/res in it. *)
                  else
                    ex1*)
            in
	    match pairing_expand t1 restl ex1 rest_lex with
	      None -> None
	    | Some(f,l') -> Some(f, List.map (fun (a,l'') -> (bl, def_list, a, t2)::l'') l')
      in

      let rec expand_res_find_list = function
	  [] -> ((fun l -> []), [])
	| ((bl, def_list, t1, t2)::restl) ->
	    let (frestl, lrestl) = expand_res_find_list restl in
	    let (f2, l2) = always_some t2 (expand_term t2) in
	    let len2 = List.length l2 in
	    ((fun l -> 
	      let (l2part, l3part) = Terms.split len2 l in
	      (bl, def_list, t1, f2 l2part) :: (frestl l3part)),
	     l2 @ lrestl)
      in 
      let (f2, l2) = expand_res_find_list l0 in
      let (f3, l3) = always_some t3 (expand_term t3) in
      let len3 = List.length l3 in
      Some((fun l -> 
	let (l3part, l2part) = Terms.split len3 l in
	let expanded_res_l = f2 l2part in
	let expanded_res_t3 = f3 l3part in
	let (f1, l1) = always_some expanded_res_l (expand_cond_find_list expanded_res_l) in
        f1 (List.map (fun l1i -> Terms.oproc_from_desc (Find(l1i, expanded_res_t3, find_info))) l1)), l3 @ l2)
  | ResE(b, t) ->
      let (f,l) = always_some t (expand_term t) in
      Some((fun l -> Terms.oproc_from_desc (Restr(b, f l))), l)
  | EventAbortE(f) ->
      (* The event is expanded to a process that stops just after the event.
	 Events in terms are used only in the RHS of equivalences, and 
	 one includes their probability of execution in the probability of
	 breaking the protocol. *)
      Some((fun l -> Terms.oproc_from_desc (EventAbort f)), [])

and expand_term_list = function
  [] -> None
| (a::l) -> 
    let aex = expand_term a in
    let lex = expand_term_list l in
    match pairing_expand a l aex lex with
      None -> None
    | Some(f,l') -> Some(f, List.map (fun (a,l'') -> a::l'') l')

and expand_pat = function
    PatVar b -> None
  | PatTuple (ft,l) -> 
      begin
	match expand_pat_list l with
	  None -> None
	| Some(f,l') -> Some(f, List.map (fun li -> PatTuple (ft,li)) l')
      end 
  | PatEqual t -> 
      begin
	match expand_term t with
	  None -> None
	| Some(f,l) -> Some (f, List.map (fun ti -> PatEqual ti) l)
      end

and expand_pat_list = function
  [] -> None
| (a::l) -> 
    let aex = expand_pat a in
    let lex = expand_pat_list l in
    match pairing_expand a l aex lex with
      None -> None
    | Some(f,l') -> Some(f, List.map (fun (a,l'') -> a::l'') l')


(* Expand process to process *)

let rec expand_process cur_array p = 
  match p.i_desc with
    Nil -> Terms.iproc_from_desc Nil
  | Par(p1,p2) -> Terms.iproc_from_desc  (Par(expand_process cur_array p1,
		      expand_process cur_array p2))
  | Repl(b,p) -> Terms.iproc_from_desc (Repl(b, expand_process (b::cur_array) p))
  | Input((c,tl),pat,p) ->
      List.iter check_no_ifletfind tl;
      begin
	let patex = expand_pat pat in
	match patex with
	  None -> 
            Terms.iproc_from_desc (Input((c,tl),pat, expand_oprocess cur_array p))
	| Some(f,l) -> 
	    Settings.changed := true;
	    let b = Terms.create_binder "patv" (Terms.new_vname()) 
		Settings.t_bitstring cur_array
	    in
	    Terms.iproc_from_desc (Input((c,tl),PatVar b, 
	      f (List.map (fun pati -> Terms.oproc_from_desc 
                  (Let(pati, Terms.term_from_binder b,
		       expand_oprocess cur_array p, Terms.oproc_from_desc Yield))) l)))
      end

and expand_oprocess cur_array p =
  match p.p_desc with 
    Yield -> Terms.oproc_from_desc Yield
  | EventAbort f -> Terms.oproc_from_desc (EventAbort f)
  | Restr(b,p) -> Terms.oproc_from_desc (Restr(b, expand_oprocess cur_array p))
  | Test(t,p1,p2) ->
	begin
	  match expand_term t with
	    None -> Terms.oproc_from_desc (Test(t,expand_oprocess cur_array p1,
			 expand_oprocess cur_array p2))
	  | Some(f,l) ->
	      Settings.changed := true;
	      f (List.map (fun ti ->
                   (* Some trivial simplifications *)
                   if Terms.is_true ti then expand_oprocess cur_array p1 else
                   if Terms.is_false ti then expand_oprocess cur_array p2 else
		   Terms.oproc_from_desc (Test(ti,expand_oprocess cur_array p1,
		        expand_oprocess cur_array p2))) l)
	end
  | Find(l0, p2, find_info) ->
      let rec expand_find_list next_f = function
	  [] -> next_f []
	| ((bl, def_list, t, p1)::rest_l) ->
	    List.iter check_no_ifletfind_br def_list;
	    let ex1 = expand_term t in
	    let ex1 = 
	      match ex1 with
		None -> None
	      | Some(f,l) ->
                  if bl != [] || def_list != [] then
                    Some(extract_elem, [final_pseudo_expand t])
                  else
                    ex1
		  (*let fNil = f (List.map (fun _ -> Terms.oproc_from_desc Yield) l) in
		  if List.exists (fun b -> Terms.refers_to_oprocess b fNil) bl || [fNil refers to variables in def_list] || [fNil contains new and bl != [] ] then
		    Some(extract_elem, [final_pseudo_expand t]) (* We cannot move the condition of the find outside, because it refers to variables defined in the find. In this case, we leave the term with if/let/find/res in it. *)
                  else
                    ex1*)
	    in
	    match ex1 with
	      None -> 
		expand_find_list (fun rest_l' ->
		  next_f ((bl, def_list, t, expand_oprocess cur_array p1)::rest_l')) rest_l
	    | Some(f,l) ->
		Settings.changed := true;
		f (List.map (fun ti -> expand_find_list (fun rest_l' ->
		  next_f ((bl, def_list, ti, expand_oprocess cur_array p1)::rest_l')) rest_l) l)
      in
      expand_find_list (fun l0' -> Terms.oproc_from_desc (Find(l0', expand_oprocess cur_array p2, find_info))) l0
  | Output((c,tl),t2,p) ->
      begin
	let tlex = expand_term_list tl in
	let t2ex = expand_term t2 in
	match pairing_expand tl t2 tlex t2ex with
	  None -> Terms.oproc_from_desc (Output((c,tl),t2, expand_process cur_array p))
	| Some(f,l) -> 
	    Settings.changed := true;
	    f (List.map (fun (t1i,t2i) -> Terms.oproc_from_desc (Output((c,t1i),t2i,expand_process cur_array p))) l)
      end
  | Let(pat,t,p1,p2) ->
      begin
	let tex = expand_term t in
	let patex = expand_pat pat in
	match pairing_expand t pat tex patex with
	  None -> Terms.oproc_from_desc (Let(pat, t, expand_oprocess cur_array p1, 
		      expand_oprocess cur_array p2))
	| Some(f,l) -> 
	    Settings.changed := true;
	    f (List.map (fun (ti,pati) -> Terms.oproc_from_desc (Let(pati,ti,expand_oprocess cur_array p1, expand_oprocess cur_array p2))) l)
      end
  | EventP(t,p) ->
      begin
	let tex = expand_term t in
	match tex with
	  None -> Terms.oproc_from_desc (EventP(t, expand_oprocess cur_array p))
	| Some(f,l) ->
	    Settings.changed := true;
	    f (List.map (fun ti -> Terms.oproc_from_desc (EventP(ti, expand_oprocess cur_array p))) l)
      end
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

(* Main function for expansion of if and find
   Call auto_sa_rename after expand_process, so that facts associated with 
   nodes are emptied, and variables defined in
   conditions of find have a single definition. 
   Expansion is called only when there is no advice pending, so we can simply 
   ignore the list of done SArenamings.
*)

let expand_process g =
  let tmp_changed = !Settings.changed in
  let (p', proba, simplif_transfos) = simplify_process g in
  let p'' = expand_process [] p' in
  if !Settings.changed then 
    let (g', proba', ins) = Transf_auto_sa_rename.auto_sa_rename { proc = p''; game_number = -1; current_queries = g.current_queries } in
    (g', proba' @ proba, ins @ (DExpandIfFind :: simplif_transfos))
  else
    begin
      Settings.changed := tmp_changed;
      Transf_auto_sa_rename.auto_sa_rename g
    end

