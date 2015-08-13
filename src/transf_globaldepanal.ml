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
open Simplify1

(* Find all variables that depend on a certain variable, provided
   these variables are not output (raises BadDep when some
   of these variables may be output)

   When tests depend on these variables, they must always yield
   the same result up to a negligible probability.

(1) Activate advice? (See comments and display of "Manual advice:" below)
Guesses some useful SArename, but makes the proof of 
event endB(x, y, na, nb) ==> beginA(x, y, na, nb) fail for 
needham-schroeder-pkcorr3BlockAuth
7/7/2008 Now, this problem seems to have disappeared

TO DO (2) The dependency analysis tends to be too sensitive to the syntax.
For example, the test let (..., =M, =A) = r always fails when M is a 
large type and A is a small type, both not depending on r, and r is random.
However, the other test let (...., x, =A) = r in if x = M then...
yields a bad dependency (comparison with the small type A).
*)

open FindCompos

let whole_game = ref { proc = Terms.iproc_from_desc Nil; game_number = -1; current_queries = [] }
let collisions_for_current_check_dependency = ref []
let local_changed = ref false
let advise = ref []

type branch = OnlyThen | OnlyElse | BothDepB | BothIndepB of term

let equal_charac_type c1 c2 =
  match (c1,c2) with
    CharacType t1, CharacType t2 -> t1 == t2
  | CharacTypeOfVar b1, CharacTypeOfVar b2 -> b1 == b2
  | _ -> false

let add_collisions_for_current_check_dependency fact_info proba_info
    (*(cur_array, true_facts, facts_info) ((t1,t2,c) as proba_info)*) =
  collisions_for_current_check_dependency :=  (fact_info, proba_info) :: (!collisions_for_current_check_dependency)

exception BadDep

let depends seen_list t = 
  List.exists (fun (b, _) -> Terms.refers_to b t) seen_list

(* find_compos b t returns true when t characterizes b: only one
value of b can yield a certain value of t *)

let find_compos_list seen_list l =
  let check (b, (st, _)) l =
    if List.exists (depends seen_list) l then
      None
    else
      Some (st, CharacTypeOfVar b)
  in
  FindCompos.find_compos_list check (Some seen_list, []) seen_list l

(* almost_indep_test seen_list t checks that the result of test t does not
depend on variables in seen_list, up to negligible probability.
Raises BadDep when the result may depend on variables in seen_list.
Returns Some true when the test is true with overwhelming probability
Returns Some false when the test is false with overwhelming probability
Returns None when the result cannot be evaluated. *)

let rec almost_indep_test cur_array true_facts fact_info seen_list t =
  match t.t_desc with
    FunApp(f,[t1;t2]) when f == Settings.f_and ->
      begin
	let t2res = almost_indep_test cur_array (t1::true_facts) fact_info seen_list t2 in
	let t1res = match t2res with
	  OnlyElse | OnlyThen -> 
	    (* I have eliminated a collision in t2 using the fact that t1 is true,
	       I won't assume t2 when analyzing t1 *)
	    almost_indep_test cur_array true_facts fact_info seen_list t1
	| BothDepB | BothIndepB _ ->
	    (* I did not eliminate any collision when analyzing t2,
	       I can swap the "and" and assume t2 when analyzing t1 *)
	    almost_indep_test cur_array (t2::true_facts) fact_info seen_list t1
	in
	match (t1res, t2res) with
	  (OnlyElse, _) | (_, OnlyElse) -> OnlyElse
	| (OnlyThen, x) -> x
	| (x, OnlyThen) -> x
	| (BothDepB, _) | (_, BothDepB) -> BothDepB
	| (BothIndepB t1, BothIndepB t2) -> BothIndepB(Terms.make_and t1 t2)
      end
  | FunApp(f,[t1;t2]) when f == Settings.f_or ->
      begin
	let t2res = almost_indep_test cur_array ((Terms.make_not t1)::true_facts) fact_info seen_list t2 in
	let t1res = match t2res with
	  OnlyElse | OnlyThen -> 
	    (* I have eliminated a collision in t2 using the fact that t1 is false,
	       I won't assume t2 when analyzing t1 *)
	    almost_indep_test cur_array true_facts fact_info seen_list t1
	| BothDepB | BothIndepB _ ->
	    (* I did not eliminate any collision when analyzing t2,
	       I can swap the "or" and assume (not t2) when analyzing t1 *)
	    almost_indep_test cur_array ((Terms.make_not t2)::true_facts) fact_info seen_list t1
	in
	match (t1res, t2res) with
	  (OnlyThen, _) | (_, OnlyThen) -> OnlyThen
	| (OnlyElse, x) -> x
	| (x, OnlyElse) -> x
	| (BothDepB, _) | (_, BothDepB) -> BothDepB
	| (BothIndepB t1, BothIndepB t2) -> BothIndepB(Terms.make_or t1 t2)
      end
  | FunApp(f,[t1]) when f == Settings.f_not ->
      begin
	match almost_indep_test cur_array true_facts fact_info seen_list t1 with
	  OnlyThen -> OnlyElse
	| OnlyElse -> OnlyThen
	| BothDepB -> BothDepB
	| BothIndepB t' -> BothIndepB (Terms.make_not t')
      end
(* Be careful: do not use or-patterns with when: 
   If both patterns of the or succeed but the when clause fails for the 
   first one and succeeds for the second one, Caml considers that the
   match fails.
*)
  | FunApp(f,[t1;t2]) 
    when ((f.f_cat == Equal) || (f.f_cat == Diff)) && (Proba.is_large_term t1 || Proba.is_large_term t2) ->
      begin
	match find_compos_list seen_list t1 with
	  Some(_, charac_type,t1',_,_) ->
	    if depends seen_list t2 then
	      BothDepB
	    else 
	      begin
                (* add probability *)
		add_collisions_for_current_check_dependency (cur_array, true_facts, fact_info) (t1', t2, charac_type);
		local_changed := true;
		if (f.f_cat == Diff) then OnlyThen else OnlyElse
	      end
	| None -> match find_compos_list seen_list t2 with
	    Some(_,charac_type,t2',_,_) ->
	    if depends seen_list t1 then
	      BothDepB
	    else 
	      begin
                (* add probability *)
		add_collisions_for_current_check_dependency (cur_array, true_facts, fact_info) (t2', t1, charac_type);
		local_changed := true;
		if (f.f_cat == Diff) then OnlyThen else OnlyElse
	      end
	  | None ->
	      if depends seen_list t then 
		BothDepB
	      else
		BothIndepB t
      end
  | _ -> 
      if depends seen_list t then 
	BothDepB 
      else
	BothIndepB t

(* checkassign1 is called when the assigned term characterizes b
   Returns false when the let is always going to take the else branch
   up to negligible probability.
   Returns true when the let can take both branches
   tmp_bad_dep is set to true when there is a bad dependency except when
   the let always takes the else branch. *)
let rec check_assign1 cur_array ((t1, t2, charac_type) as proba_info) vars_to_add tmp_bad_dep seen_list st = function
    PatVar b ->
      begin
	let charac_type' = 
	  if st = Decompos then CharacType b.btype else charac_type 
	in
	try 
	  let (st',proba_info_list) = List.assq b (!seen_list) in
	  if st != st' then
	    tmp_bad_dep := true
	  else if not (List.exists (fun (t1', t2', charac_type'') ->
	    (matches_pair t1' t2' t1 t2) &&
	    (equal_charac_type charac_type' charac_type'')) (!proba_info_list))
	  then
	    begin
	      (* Above, I use "matches_pair" to check that t1 = t2 is
                 a particular case of the assignment t1' = t2' seen before.
                 If this is true, I have nothing to add.
                 (Testing equality (t1,t2) = (t1',t2') is not exactly 
		 what we want because these terms may contain wildcards "?")
	      Display.display_binder b;
	      print_newline();
	      print_string " Already present: ";
	      List.iter (fun (t1', t2', charac_type'') ->
		Display.display_term t1';
		print_string ", ";
		Display.display_term t2';
		print_string ", ";
		begin
		match charac_type'' with
		  CharacType t -> print_string t.tname
		| CharacTypeOfVar b -> Display.display_binder b
		end;
		print_newline()) (!proba_info_list);
	      print_string "Adding: ";
	      Display.display_term t1;
	      print_string ", ";
	      Display.display_term t2;
	      print_string ", ";
	      begin
		match charac_type' with
		  CharacType t -> print_string t.tname
		| CharacTypeOfVar b -> Display.display_binder b
	      end;
	      print_newline();
	      *)
	      proba_info_list := (t1, t2, charac_type') :: (!proba_info_list)
	    end
	with Not_found ->
	  vars_to_add := (b,(st, ref [t1, t2, charac_type'])) :: (!vars_to_add)
      end;
      true
  | PatTuple(f,l) ->
      if st != Decompos then tmp_bad_dep := true;
      List.for_all (check_assign1 cur_array proba_info vars_to_add tmp_bad_dep seen_list st) l
  | PatEqual t ->
      if (depends (!seen_list) t) || 
        (not (Proba.is_large_term t)) then
	begin
	  tmp_bad_dep := true;
	  true
	end
      else
	begin
	  (* add probability *)
	  add_collisions_for_current_check_dependency (cur_array, [], t.t_facts) proba_info;
	  false
	end

(* check_assign2 is called when the assigned term does not depend on b
   Returns Some(charac_type, t') when the let is always going to take the 
   else branch up to negligible probability. t' is the term with which
   the collision is eliminated and charac_type the type of the part of 
   t' characterized by the value of the pattern.
   Returns None when the let can take both branches 
   tmp_bad_dep is set to true when there is a bad dependency except when
   the let always takes the else branch. *)
let rec check_assign2 seen_list to_advise tmp_bad_dep = function
    PatVar b ->
      if List.exists (fun (b',_) -> b == b') (!seen_list) then
	begin
	  to_advise := Terms.add_eq (SArenaming b) (!to_advise);
	  tmp_bad_dep := true
	end;
      None
  | PatTuple(f,l) ->
      begin
        match check_assign2_list seen_list to_advise tmp_bad_dep l with
	  None -> None
	| Some(charac_type, l') ->
	    Some (charac_type, Terms.build_term_type (snd f.f_type) (FunApp(f,l')))
      end
  | PatEqual t ->
      match find_compos_list (!seen_list) t with
	Some (status, charac_type,t',_,_) when Proba.is_large_term t ->
	  Some(charac_type, t')
      |	_ ->
	begin
	  if depends (!seen_list) t then
	    tmp_bad_dep := true;
	  None
	end

and check_assign2_list seen_list to_advise tmp_bad_dep = function
    [] -> None
  | (a::l) ->
      match check_assign2 seen_list to_advise tmp_bad_dep a with
	None -> 
	  begin
	    match check_assign2_list seen_list to_advise tmp_bad_dep l with
	      None -> None
	    | Some(charac_type, l') -> Some(charac_type, (any_term_pat a)::l')
	  end
      |	Some(charac_type, a') -> Some(charac_type, a'::(List.map any_term_pat l))

let rec check_depend_process cur_array seen_list p' =
  match p'.i_desc with
    Nil -> Terms.iproc_from_desc Nil
  | Par(p1,p2) -> 
      let p1' = check_depend_process cur_array seen_list p1 in
      let p2' = check_depend_process cur_array seen_list p2 in
      Terms.iproc_from_desc (Par(p1',p2'))
  | Repl(b,p) -> 
      Terms.iproc_from_desc (Repl(b,check_depend_process (b::cur_array) seen_list p))
  | Input((c,tl),pat,p) -> 
      if List.exists (depends (!seen_list)) tl then raise BadDep;
      (* Create a dummy variable for the input message *)
      let b = Terms.create_binder "dummy_input" (Terms.new_vname())
		(Terms.term_from_pat pat).t_type
		cur_array
      in
      let t2 = Terms.term_from_binder b in
      let tmp_bad_dep = ref false in
      let to_advise = ref [] in
      match check_assign2 seen_list to_advise tmp_bad_dep pat with
	Some(charac_type, t1) -> 
	  add_collisions_for_current_check_dependency (cur_array, [], p'.i_facts) (t1, t2, charac_type);
	  local_changed := true;
	  Terms.iproc_from_desc (Input((c, tl), PatVar b, Terms.oproc_from_desc Yield))
      |	None ->
	begin
	  if (!tmp_bad_dep) then
	    begin
	      if (!to_advise) != [] then
		begin
                  if !Settings.no_advice_globaldepanal then 
                    begin
		      print_string "Manual advice: ";
		      Display.display_list Display.display_instruct (!to_advise);
		      print_newline()
                    end
                  else
		    List.iter (fun x -> advise := Terms.add_eq x (!advise)) (!to_advise)
		end;
	      raise BadDep
	    end;
	  Terms.iproc_from_desc (Input((c,tl), pat, check_depend_oprocess cur_array seen_list p))
	end

and check_depend_oprocess cur_array seen_list p = 
  match p.p_desc with
    Yield -> Terms.oproc_from_desc Yield
  | EventAbort f -> Terms.oproc_from_desc (EventAbort f)
  | Restr(b,p) -> 
      Terms.oproc_from_desc (Restr(b, check_depend_oprocess cur_array seen_list p))
  | Test(t,p1,p2) -> 
      begin
	match almost_indep_test cur_array [] t.t_facts (!seen_list) t with
	  BothDepB -> raise BadDep
	| BothIndepB t' -> 
	    let p1' = check_depend_oprocess cur_array seen_list p1 in
	    let p2' = check_depend_oprocess cur_array seen_list p2 in
	    Terms.oproc_from_desc (Test(t', p1',p2'))
	| OnlyThen -> 
	    local_changed := true;
	    check_depend_oprocess cur_array seen_list p1
	| OnlyElse -> 
	    local_changed := true;
	    check_depend_oprocess cur_array seen_list p2
      end
  | Find(l0,p2,find_info) ->
      let always_then = ref false in
      let check_br (b,l) = 
	if List.exists (depends (!seen_list)) l then raise BadDep 
      in
      let l0' = ref [] in
      List.iter (fun (bl,def_list,t,p1) ->
	List.iter check_br def_list;
	let bl' = List.map snd bl in
	(* Compute the probability that the test fails.*)
	let t_facts = match p.p_facts with
	  None -> None
	| Some (true_facts, def_vars, above_node) ->
	    let def_vars' = ref [] in
	    List.iter (Terms.close_def_subterm def_vars') def_list;
	    Some(true_facts, (!def_vars') @ def_vars, above_node)
	in
        match almost_indep_test (bl' @ cur_array) [] t_facts (!seen_list) t with
	  BothDepB -> raise BadDep
	| OnlyThen ->
	    if def_list == [] then always_then := true;
	    l0' := (bl, def_list, t, check_depend_oprocess cur_array seen_list p1) :: (!l0')
	| BothIndepB t' ->
            l0' := (bl, def_list, t', check_depend_oprocess cur_array seen_list p1) :: (!l0')
	| OnlyElse -> 
	    local_changed := true;
	    ()) l0;
      if !always_then then
	begin
	  local_changed := true;
	  Terms.oproc_from_desc (Find(!l0', Terms.oproc_from_desc Yield, find_info))
	end
      else
	Terms.oproc_from_desc (Find(!l0', check_depend_oprocess cur_array seen_list p2, find_info))
  | Output((c,tl),t2,p) ->
      if (List.exists (depends (!seen_list)) tl) || (depends (!seen_list) t2) then raise BadDep;
      Terms.oproc_from_desc (Output((c,tl),t2, check_depend_process cur_array seen_list p))
  | Let(pat,t,p1,p2) ->
      begin
	match find_compos_list (!seen_list) t with
	  Some (st, charac_type,t',_,_) ->
	    begin
	      let vars_to_add = ref [] in
	      let tmp_bad_dep = ref false in
	      if check_assign1 cur_array (t', Terms.term_from_pat pat, charac_type) vars_to_add tmp_bad_dep seen_list st pat then
		begin
		  if (!tmp_bad_dep) || (match pat with PatVar _ -> false | _ -> true) then raise BadDep;
		  List.iter (function ((b,_) as b_st) ->
                    (*print_string "Adding ";
                      Display.display_binder b0;
                      print_newline();*)
		    if not (Terms.is_assign b) then
		      raise BadDep;
		    seen_list := b_st :: (!seen_list)) (!vars_to_add);
		  let p1' = check_depend_oprocess cur_array seen_list p1 in
		  let p2' = check_depend_oprocess cur_array seen_list p2 in
		  Terms.oproc_from_desc (Let(pat, t, p1', p2'))
		end
	      else
		begin
		  local_changed := true;
		  check_depend_oprocess cur_array seen_list p2
		end
	    end
	| None ->
	    if depends (!seen_list) t then
	      raise BadDep
	    else
	      begin
		let to_advise = ref [] in
		let tmp_bad_dep = ref false in
		match check_assign2 seen_list to_advise tmp_bad_dep pat with
		  Some(charac_type, t1) ->
		    (* add probability *)
		    add_collisions_for_current_check_dependency (cur_array, [], p.p_facts) (t1, t, charac_type);
		    local_changed := true;
		    check_depend_oprocess cur_array seen_list p2
		| None ->
		  begin
		    if (!tmp_bad_dep) then
		      begin
			if (!to_advise) != [] then
			  begin
			    if !Settings.no_advice_globaldepanal then 
			      begin
				print_string "Manual advice: ";
				Display.display_list Display.display_instruct (!to_advise);
				print_newline()
			      end
			    else
			       List.iter (fun x -> advise := Terms.add_eq x (!advise)) (!to_advise)
			  end;
			raise BadDep
		      end;
		    let p1' = check_depend_oprocess cur_array seen_list p1 in
		    let p2' = check_depend_oprocess cur_array seen_list p2 in
		    Terms.oproc_from_desc (Let(pat, t, p1', p2'))
		  end
	      end
      end
  | EventP(t,p) ->
      Terms.oproc_from_desc (EventP(t, check_depend_oprocess cur_array seen_list p))
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

let rec check_depend_iter seen_list =
  if List.exists (fun (b0, _) -> Settings.occurs_in_queries b0) (!seen_list) then
    raise BadDep;
  collisions_for_current_check_dependency := [];
  local_changed := false;
  let old_seen_list = !seen_list in
  let proc' = check_depend_process [] seen_list (!whole_game).proc in
  if (!seen_list) != old_seen_list then check_depend_iter seen_list else proc'

let rec get_type_from_charac seen_list vlist = function
    CharacType t -> [t]
  | CharacTypeOfVar b -> 
      if List.memq b seen_list then
	raise BadDep;
      let (st, proba_info_list) = List.assq b vlist in
      List.concat (List.map (fun (_,_,charac_type) -> get_type_from_charac (b::seen_list) vlist charac_type) (!proba_info_list))

let check_all_deps b0 g =
  whole_game := g;
  let vcounter = !Terms.vcounter in
  try
    let dummy_term = Terms.term_from_binder b0 in
    let b0st = (b0, (Decompos, ref [dummy_term, dummy_term, CharacType b0.btype])) in
    let seen_vars = ref [b0st] in
    let proc' = check_depend_iter seen_vars in
    let res_game = { proc = proc'; game_number = -1; current_queries = g.current_queries } in
    if not (!local_changed) then 
      raise BadDep;
    let vars_charac_type = 
      List.map (fun (b, (st, proba_info_list)) -> (b, List.concat (List.map (fun (_,_,charac_type) -> get_type_from_charac [b] (!seen_vars) charac_type) (!proba_info_list)))) (!seen_vars)
    in    
    let collisions = ref [] in
    List.iter (fun ((cur_array, true_facts, facts_info),(t1,t2,c)) -> 
      let tl = 
	match c with
	  CharacType t -> [t]
	| CharacTypeOfVar b -> List.assq b vars_charac_type
      in
      (* Compute the used indices *)
      let used_indices_ref = ref [] in
      Proba.collect_array_indexes used_indices_ref t1;
      Proba.collect_array_indexes used_indices_ref t2;
      let used_indices = !used_indices_ref in
      if List.for_all (fun t -> 
	Proba.is_small_enough_coll_elim (used_indices, t)
	  ) tl then
	collisions := ((cur_array, []), (t1,t2,tl)) :: (!collisions)
      else
	try
	  let true_facts' = true_facts @ (Facts.get_facts_at facts_info) in
	  collisions := ((cur_array, true_facts'), (t1,t2,tl)) :: (!collisions)
	with Contradiction -> ()
	    ) (!collisions_for_current_check_dependency);
    Some(res_game, !collisions)
  with BadDep -> 
    Terms.vcounter := vcounter; (* Forget variables when fails *)
    None

let main b0 coll_elim g =
  Simplify1.reset coll_elim g;
  Terms.array_ref_process g.proc;
  Terms.build_def_process None g.proc;
  let dummy_term = Terms.term_from_binder b0 in
  if not ((Terms.is_restr b0) && (Proba.is_large_term dummy_term)) then
    (g, [], []) 
  else
    begin
    advise := [];
    let res = check_all_deps b0 g in
    (* Transfer the local advice to the global advice in Settings.advise *)
    List.iter (fun x -> Settings.advise := Terms.add_eq x (!Settings.advise)) (!advise);
    advise := [];
    match res with
      None -> (g, [], []) 
    | Some(res_game, collisions) ->
	if not (List.for_all (fun ((cur_array, true_facts),(t1,t2,tl)) ->
	  add_term_collisions (cur_array, true_facts, []) t1 t2 b0 None tl) collisions) then
	  (g, [], [])
	else
	  begin
	    Settings.changed := true;
	    let proba = final_add_proba() in
	    (res_game, proba, [DGlobalDepAnal(b0,coll_elim)])
	  end
    end
