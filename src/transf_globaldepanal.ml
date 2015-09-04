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
open Simplify1

(* Find all variables that depend on a certain variable [b0], provided
   these variables are not output (raises BadDep when some
   of these variables may be output)

   When tests depend on these variables, they must be simplified (by
   eliminating collisions that have a negligible probability) into
   tests that do not depend on these variables (otherwise, it raises BadDep).

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

(* The main variable on which we perform the dependency analysis (b0) *)
let main_var = ref (Terms.create_binder "dummy" 0 Settings.t_bitstring [])

(* List of variables that depend on the main variable b0.
   The list contains triples (b, (status, (ref [(t1,t2,charac_type);...], ref args_opt))) 
   meaning that b depends on b0, 
   when args_opt is (Some l), b[args_at_creation] depends on b0[l]
   and on no other cell of b0
   when args_opt is None, b may depend on any cell of b0. *)
let dvar_list = ref []

(* The flag [dvar_list_changed] is set when [dvar_list] has been changed
   since the last iteration. A new iteration of dependency analysis 
   is then needed. *)
let dvar_list_changed = ref false

(* List of variables know to be defined at some point *)
let defvar_list = ref []

(* The flag [defvar_list_changed] is set when [defvar_list] has been
   changed since the last iterattion. A new iteration of dependency analysis
   is then needed. *)
let defvar_list_changed = ref false

(* [vars_charac_type] associates to each variable [b] that depends on [b0]
   a list of types, containing one type [t] for each way to compute [b] from [b0].
   The value of [b] characterizes a part of [b0] of type [t], when [b] is computed
   in that way from [b0]. *)
let vars_charac_type = ref []

(* The flag [local_changed] is set when the dependency analysis
   managed to simplify the game *)
let local_changed = ref false

(* The flag [defined_condition_update_needed] is set when the dependency analysis
   modified a term is such a way that a defined condition
   of a previous find may need to be updated. *)
let defined_condition_update_needed = ref false

(* Advised instructions *)
let advise = ref []

(* [add_advice new_advice] adds [new_advice] to the list
   of advised instructions [advise] *)

let add_advice new_advice =
  if !Settings.no_advice_globaldepanal then 
    begin
      print_string "Manual advice: ";
      Display.display_list Display.display_instruct new_advice;
      print_newline()
    end
  else
    List.iter (fun x -> advise := Terms.add_eq x (!advise)) new_advice

(* This exception is raised when the global dependency analysis fails *)
exception BadDep

type branch = OnlyThen | OnlyElse | BothDepB | BothIndepB of term

let equal_charac_type c1 c2 =
  match (c1,c2) with
    CharacType t1, CharacType t2 -> t1 == t2
  | CharacTypeOfVar b1, CharacTypeOfVar b2 -> b1 == b2
  | _ -> false

(* [get_type_from_charac seen_list c] determines which type(s) [c] refers to:
   when [c = CharacType t], it is [t];
   when [c = CharacTypeOfVar b], it is the type(s) of the part(s) of [b0] that [b] characterizes.
   This function uses information in [dvar_list] to determine the type of the part of [b0] 
   that variables characterize.
   This function is used to compute [vars_charac_type]. 
   [seen_list] stores to list of variables that already been seen during
   recursive calls to [get_type_from_charac]. It serves to avoid an 
   infinite loop. *)

let rec get_type_from_charac seen_list = function
    CharacType t -> [t]
  | CharacTypeOfVar b -> 
      if List.memq b seen_list then
	begin
	  print_string "Loop in variable dependencies.\n";
	  raise BadDep
	end;
      let (st, (proba_info_list,_,_)) = List.assq b (!dvar_list) in
      List.concat (List.map (fun (_,_,charac_type) -> get_type_from_charac (b::seen_list) charac_type) (!proba_info_list))

(* [get_type_from_charac2 c] determines which type(s) [c] refers to,
   like [get_type_from_charac], but it uses the information stored
   in [vars_charac_type].
   This function must be called only when [vars_charac_type] is up-to-date,
   so [dvar_list] has not changed. *)
      
let get_type_from_charac2 = function
    CharacType t -> [t]
  | CharacTypeOfVar b -> List.assq b (!vars_charac_type)

(* [add_collisions_for_current_check_dependency (cur_array, true_facts, facts_info) (t1,t2,c)] 
   takes into account the probability of collision between [t1] and [t2]. 
   [c] determines the type of the part of [b0] that [t1] characterizes.
   [true_facts] and [facts_info] indicate facts that are known to be true.
   These facts are used to optimize the computation of the probability
   (to get a smaller probability).
   [add_collisions_for_current_check_dependency] raises [BadDep] when the 
   obtained probability is too large, so this collision cannot be eliminated. *)

let add_collisions_for_current_check_dependency (cur_array, true_facts, facts_info) (t1,t2,c) =
  (* If [dvar_list] has changed, we are going to iterate any way,
     no need to compute probabilities. Furthermore, [vars_charac_type]
     may not be up-to-date wrt to [dvar_list], possibly leading to an error
     in [get_type_from_charac2]. *)
  if !dvar_list_changed then () else
  let tl = get_type_from_charac2 c in
  (* Compute the used indices *)
  let used_indices_ref = ref [] in
  Proba.collect_array_indexes used_indices_ref t1;
  Proba.collect_array_indexes used_indices_ref t2;
  let used_indices = !used_indices_ref in
  try
    let true_facts' = 
      (* We optimize the speed of the system by not computing
	 [true_facts'] when the probability of collision
	 is small enough that it can be accepted without 
	 trying to eliminate some of the [used_indices].
	 (The facts in [true_facts'] are used only for that.) *)
      if List.for_all (fun t -> 
	Proba.is_small_enough_coll_elim (used_indices, t)
	  ) tl then
	[]
      else
	true_facts @ (Facts.get_facts_at facts_info) 
    in
    if not (Simplify1.add_term_collisions (cur_array, true_facts', [], Terms.make_true()) t1 t2 (!main_var) None tl) then
      begin
	print_string "Probability of collision between ";
	Display.display_term t1;
	print_string " and ";
	Display.display_term t2;
	print_string " too big.\n";
	raise BadDep
      end
  with Contradiction -> ()

(* [add_collisions_for_current_check_dependency2] is similar to
   [add_collisions_for_current_check_dependency].
   Three differences:
   - In [add_collisions_for_current_check_dependency], the known facts come both from
   [true_facts] and [facts_info], and a list of known facts must be computed from that.
   In [add_collisions_for_current_check_dependency2] the known facts are already computed
   in [true_facts].
   - In [add_collisions_for_current_check_dependency], any cell of [b0] may be 
   characterized by [t1].
   In [add_collisions_for_current_check_dependency2], the particular cell of [b0]
   characterized by [t1] may be indicated by [index_opt]. [side_condition] indicates
   a condition needed to make sure that [t2] does not depend on this particular cell of [b0].
   - [add_collisions_for_current_check_dependency2] returns [true] when the probability of
   collision is small enough so that the collision can be eliminated, and [false]
   otherwise. *)

let add_collisions_for_current_check_dependency2 cur_array true_facts side_condition (t1,t2,c) index_opt =
  (* If [dvar_list] has changed, we are going to iterate any way,
     no need to compute probabilities. Furthermore, [vars_charac_type]
     may not be up-to-date wrt to [dvar_list], possibly leading to an error
     in [get_type_from_charac2]. *)
  if !dvar_list_changed then true else
  let tl = get_type_from_charac2 c in
  Simplify1.add_term_collisions (cur_array, true_facts, [], side_condition) t1 t2 (!main_var) index_opt tl

(* [depends t] returns [true] when [t] may depend on [b0] *)

let depends t = 
  List.exists (fun (b, _) -> Terms.refers_to b t) (!dvar_list)

(* [defined t] returns [true] when [t] may be defined *)

let rec defined t =
  match t.t_desc with
    FunApp(f,l) -> List.for_all defined l
  | Var(b,l) ->
      (List.memq b (!defvar_list)) &&
      (List.for_all defined l)
  | ReplIndex _ -> true
  | _ -> Parsing_helper.internal_error "Only Var/FunApp/ReplIndex should appear in Transf_globaldepanal.defined"

(* [defined_br (b,l)] returns [true] when [b[l]] may be defined *)

let defined_br (b,l) =
  (List.memq b (!defvar_list)) &&
  (List.for_all defined l)

(* [add_defined b] adds the variable [b] to the list of defined variables

   Note: the variables defined inside terms in conditions of find
   must not have array accesses. Hence, I do not need to scan these
   terms to add their bound variables to the list of defined variables. *)

let add_defined b =
  if not (List.memq b (!defvar_list)) then
    begin
      defvar_list := b :: (!defvar_list);
      defvar_list_changed := true
    end

(* [add_defined_pat pat] adds all variables bound by the pattern [pat] 
   to the list of defined variables *)

let rec add_defined_pat = function
    PatVar b -> add_defined b
  | PatTuple(f,l) -> List.iter add_defined_pat l
  | PatEqual _ -> ()

(* [find_compos_list t] returns [Some(st,charac_type,t',l_opt')]
   when [t] characterizes a part of [b0] of type determined by [charac_type]
   (i.e. only one value of that part of [b0] can yield a certain value of [t];
   [st] is 
        - [Compos] when [t] is obtained from [b0] by first applying
        poly-injective functions (functions marked [compos]), then
        functions that extract a part of their argument 
        (functions marked [uniform]).
        - [Decompos] when [t] is obtained from [b0] by applying functions
        that extract a part of their argument (functions marked [uniform])
   [t'] is a modified version of the term [t] in which the parts not
   useful to show that [t] characterizes a part of [b0] are replaced with
   fresh variables.
   [l_opt'] is [Some l] when [t] characterizes a part of the cell [b0[l]]
           and [None] when [t] characterizes a part of some unknown cell of [b0]. *)

let rec find_compos_rec t0 t =
  match t.t_desc with
    Var(b,l) when not (List.exists depends l) ->
      begin
        try 
          let (_,(_,(_,charac_args_opt,_))) as b_st = (b, List.assq b (!dvar_list)) in
          let check (b, (st, _)) tl =
            if Terms.equal_term_lists l tl then
              Some (st, CharacTypeOfVar b)
            else
              None
          in
          match FindCompos.find_compos check ((!main_var), (Some (!dvar_list), [])) b_st t0 with
	    Some(st,charac_type,t') -> 
	      let l_opt' = 
		match !charac_args_opt with
		  None -> None
		| Some b0_ind ->
		    (* b[args_at_creation] characterizes b0[b0_ind] *)
                    let l' = List.map (Terms.subst b.args_at_creation l) b0_ind (* b0_ind{l/b.args_at_creation} *) in
		    (* t0 characterizes b[l], so it characterizes b0[l'] *)
		    Some l'
	      in
	      Some(st,charac_type,t',l_opt')
	  | None -> None
	with Not_found ->
	  None
      end
  | FunApp(f,l) ->
      Terms.find_some (find_compos_rec t0) l
  | _ -> None

let find_compos_list t = find_compos_rec t t


(* This exception is raised by [get_dep_indices] when [t] actually depends on [b0]
   for unspecified indices *)
exception Depends

(* [get_dep_indices collect_bargs t] collects in [collect_bargs] the
   indices of [b0] such that [t] depends on the values of [b0] only at
   the indices in [collect_bargs]. If it is impossible to find such
   [collect_bargs], it raises Depends. *)

let rec get_dep_indices collect_bargs t =
  match t.t_desc with
    FunApp(f,l) -> List.iter (get_dep_indices collect_bargs) l
  | ReplIndex(b) -> ()
  | Var(b,l) ->
      begin
        (* Index variables cannot depend on [b0].
	   For safety, I verify that. *)
	List.iter (fun t' ->
	  assert (not(depends t'))
	    ) l;
        try
          let (_,(_,_,depend_args_opt)) = List.assq b (!dvar_list) in
	  match !depend_args_opt with
	    Some b0_ind ->
	      (* b[args_at_creation] depends only on b0[b0_ind] *)
	      let l' = List.map (Terms.subst b.args_at_creation l) b0_ind (* b0_ind{l/b.args_at_creation} *) in
              (* The access to b[l] depends only on b0[l'],
                 while the other term of the equality characterizes b0[l0] *)
	      if not (List.exists (List.for_all2 Terms.equal_terms l') (!collect_bargs)) then
		collect_bargs := l' :: (!collect_bargs)
	  | _ -> raise Depends
        with Not_found ->
	  ()
      end
  | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in get_dep_indices"

(* [dependency_collision_rec cur_array true_facts t1 t2 t] simplifies [t1 = t2]
using dependency analysis. Basically, when [t1] characterizes a part of [b0]
and [t2] does not depend on [b0], the equality has a negligible probability
to hold, so it can be simplified into [false]. 
[dependency_collision_rec] extends this simplification to the case in which
[t1] characterizes a part of a certain cell of [b0] and [t2] does not depend
on that cell, possibly by adding assumptions that certain array indices are different.
It returns
- [Some t'] when it simplified [t1 = t2] into [t'];
- [None] when it could not simplify [t1 = t2]. 
[cur_array] is the list of current replication indices at [t1 = t2].
[true_facts] is a list of facts that are known to hold.
[t] is a subterm of [t1] that contains the variable characterized by [t1].
(Initially, [t = t1], and recursive calls are made until [t] is just a variable.)
 *)

let rec dependency_collision_rec cur_array true_facts t1 t2 t =
  match t.t_desc with
    Var(b,l) when not (List.exists depends l) ->
      begin
        try 
          let (_,(_,(_,charac_args_opt,_))) as b_st = (b, List.assq b (!dvar_list)) in
          let check (b, (st, _)) tl =
            if Terms.equal_term_lists l tl then
              Some (st, CharacTypeOfVar b)
            else
              None
          in
          match FindCompos.find_compos check ((!main_var), (Some (!dvar_list), [])) b_st t1 with
            Some(_, charac_type, t1') -> 
	      begin
		match !charac_args_opt with
		  Some b0_ind ->
		    (* b[args_at_creation] characterizes b0[b0_ind] *)
                    let l' = List.map (Terms.subst b.args_at_creation l) b0_ind (* b0_ind{l/b.args_at_creation} *) in
		    (* t1 characterizes b[l], so it characterizes b0[l'] *)
		    let collect_bargs = ref [] in
		    get_dep_indices collect_bargs t2;
		    if List.exists (List.for_all2 Terms.equal_terms l') (!collect_bargs) then
		      (* If t2 depends on b0[l'], we cannot eliminate collisions *)
	              raise Depends;
		    let side_condition = 
		      Terms.make_and_list (List.map (fun l'' ->
			Terms.make_or_list (List.map2 Terms.make_diff l' l'')
			  ) (!collect_bargs))
		    in
	            (* add probability; returns true if small enough to eliminate collisions, false otherwise. *)
		    if add_collisions_for_current_check_dependency2 cur_array true_facts side_condition (t1',t2,charac_type) (Some l') then
		      let res = 
			Terms.make_or_list (List.map (fun l'' ->   
			let t2'' = Terms.replace l'' l' t2 in
			Terms.make_and (Terms.make_and_list (List.map2 Terms.make_equal l' l'')) (Terms.make_equal t1 t2'')
			  ) (!collect_bargs))
		      in
		      (*print_string "Simplified ";
		      Display.display_term t1;
		      print_string " = ";
		      Display.display_term t2;
		      print_string " into ";
		      Display.display_term res;
		      print_newline();*)
		      Some res
		    else
		      None
		| None -> 
		    (* b[args_at_creation] characterizes b0 for some unknown indices *)
		    let collect_bargs = ref [] in
		    get_dep_indices collect_bargs t2;
                    if !collect_bargs != [] then
                      (* if [t2] depends on [b0], the dependency analysis fails to
			 eliminate the required collisions *)
		      None
	            (* add probability; returns true if small enough to eliminate collisions, false otherwise. *)
		    else if add_collisions_for_current_check_dependency2 cur_array true_facts (Terms.make_true()) (t1',t2,charac_type) None then
		      begin
		      (*print_string "Simplified ";
		      Display.display_term t1;
		      print_string " = ";
		      Display.display_term t2;
		      print_string " into false\n";*)
		      Some (Terms.make_false())
		      end
		    else
		      None
	      end
          | _ -> None
	with Not_found | Depends -> 
	  None
      end
  | FunApp(f,l) ->
      Terms.find_some (dependency_collision_rec cur_array true_facts t1 t2) l
  | _ -> None

(* [dependency_collision cur_array simp_facts t1 t2] simplifies [t1 = t2]
using dependency analysis.
It returns
- [Some t'] when it simplified [t1 = t2] into [t'];
- [None] when it could not simplify [t1 = t2]. 
[cur_array] is the list of current replication indices at [t1 = t2].
[simp_facts] contains facts that are known to hold. *)

let dependency_collision cur_array simp_facts t1 t2 = 
  let t1' = try_no_var_rec simp_facts t1 in
  let t2' = try_no_var_rec simp_facts t2 in
  let true_facts = true_facts_from_simp_facts simp_facts in
  match dependency_collision_rec cur_array true_facts t1' t2' t1' with
    (Some _) as x -> x
  | None -> dependency_collision_rec cur_array true_facts t2' t1' t2'


(* [almost_indep_test cur_array true_facts fact_info t] 
   checks that the result of test [t] does not depend on 
   variables in [dvar_list], up to negligible probability.
Returns
- BothDepB when the result may depend on variables in [dvar_list];
- OnlyThen when the test is true with overwhelming probability;
- OnlyElse when the test is false with overwhelming probability;
- BothIndepB t' when the result does not depend on variables in [dvar_list] and is equal to [t']. 
[cur_array] is the list of current replication indices at [t].
[true_facts] is a list of facts that are known to be true,
because [t] occur in a conjunction or disjunction, so it is
evaluated only when the facts in [true_facts] are true.
[fact_info] indicates the true facts and defined variables at [t].
*)

let rec almost_indep_test cur_array true_facts fact_info t =
  match t.t_desc with
    FunApp(f,[t1;t2]) when f == Settings.f_and ->
      begin
	let t2res = almost_indep_test cur_array (t1::true_facts) fact_info t2 in
	let t1res = match t2res with
	  OnlyElse -> 
            (* t2 is always false, the value of t1 does not matter *) 
	    BothDepB
	| OnlyThen -> 
	    (* I have eliminated a collision in t2 using the fact that t1 is true,
	       I won't assume t2 when analyzing t1 *)
	    almost_indep_test cur_array true_facts fact_info t1
	| BothDepB ->
	    (* I did not eliminate any collision when analyzing t2,
	       I can swap the "and" and assume t2 when analyzing t1 *)
	    almost_indep_test cur_array (t2::true_facts) fact_info t1
	| BothIndepB t2' ->
	    (* I can swap the "and" after simplification of t2
	       and assume t2' when analyzing t1 *)
	    almost_indep_test cur_array (t2'::true_facts) fact_info t1
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
	let t2res = almost_indep_test cur_array ((Terms.make_not t1)::true_facts) fact_info t2 in
	let t1res = match t2res with
	  OnlyElse -> 
	    (* I have eliminated a collision in t2 using the fact that t1 is false,
	       I won't assume (not t2) when analyzing t1 *)
	    almost_indep_test cur_array true_facts fact_info t1
	| OnlyThen ->
	    (* t2 is always true, the value of t1 does not matter *)
	    BothDepB
	| BothDepB ->
	    (* I did not eliminate any collision when analyzing t2,
	       I can swap the "or" and assume (not t2) when analyzing t1 *)
	    almost_indep_test cur_array ((Terms.make_not t2)::true_facts) fact_info t1
	| BothIndepB t2' ->
	    (* I can swap the "or" after simplification of t2
	       and assume (not t2') when analyzing t1 *)
	    almost_indep_test cur_array ((Terms.make_not t2')::true_facts) fact_info t1
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
	match almost_indep_test cur_array true_facts fact_info t1 with
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
	match find_compos_list t1 with
	  Some(_, charac_type,t1',_) ->
	    if depends t2 then
	      BothDepB
	    else 
	      begin
                (* add probability *)
		add_collisions_for_current_check_dependency (cur_array, true_facts, fact_info) (t1', t2, charac_type);
		local_changed := true;
		if (f.f_cat == Diff) then OnlyThen else OnlyElse
	      end
	| None -> match find_compos_list t2 with
	    Some(_,charac_type,t2',_) ->
	    if depends t1 then
	      BothDepB
	    else 
	      begin
                (* add probability *)
		add_collisions_for_current_check_dependency (cur_array, true_facts, fact_info) (t2', t1, charac_type);
		local_changed := true;
		if (f.f_cat == Diff) then OnlyThen else OnlyElse
	      end
	  | None ->
	      if depends t then 
		BothDepB
	      else
		BothIndepB t
      end
  | _ -> 
      if depends t then 
	BothDepB 
      else
	BothIndepB t

(* [almost_indep_test cur_array t] 
   checks that the result of test [t] does not depend on 
   variables in [dvar_list], up to negligible probability.
Returns
- BothDepB when the result may depend on variables in [dvar_list];
- OnlyThen when the test is true with overwhelming probability;
- OnlyElse when the test is false with overwhelming probability;
- BothIndepB t' when the result does not depend on variables in [dvar_list] and is equal to [t']. 
[cur_array] is the list of current replication indices at [t].
*)

let almost_indep_test cur_array t =
  (* Call a fast version of almost_indep_test first. *)
  let res = almost_indep_test cur_array [] t.t_facts t in
  if res != BothDepB then res else
  (* In case this version is not sufficient to eliminate the dependency,
     use a more costly and more precise version *)
  try
    let true_facts = Facts.get_facts_at t.t_facts in
    let simp_facts = Facts.simplif_add_list (dependency_collision cur_array) ([],[],[]) true_facts in
    let t' = Facts.simplify_term (dependency_collision cur_array) simp_facts t in
    (*print_string ("At " ^ (string_of_int t.t_occ) ^ ", the term ");
    Display.display_term t;
    print_string " is simplified into ";
    Display.display_term t';
    print_newline();*)
    if Terms.is_true t' then 
      OnlyThen
    else if Terms.is_false t' then
      OnlyElse
    else if depends t' then
      begin
	print_string ("At " ^ (string_of_int t.t_occ) ^ ", the term ");
	Display.display_term t;
	if Terms.synt_equal_terms t t' then
	  print_string (" depends on " ^ (Display.binder_to_string (!main_var)) ^ "\n")
	else
	  begin
	    print_string " is simplified into ";
	    Display.display_term t';
	    print_string (", but still depends on " ^ (Display.binder_to_string (!main_var)) ^ "\n")
	  end;
	BothDepB
      end
    else
      BothIndepB (Terms.move_occ_term t')
  with Contradiction ->
    (* The term [t] is in fact unreachable *)
    OnlyElse

(* [convert_to_term pat] converts the pattern [pat] into a term,
   when [pat] does not bind variables.
   When [pat] binds variables, it raises [Not_found] *)

let rec find_facts = function
    [] -> None
  | t::l ->
      if t.t_facts == None then find_facts l else t.t_facts

let find_map = function
    [] -> Terms.map_empty
  | t::_ -> t.t_incompatible

let rec convert_to_term = function
    PatVar _ -> raise Not_found
  | PatTuple(f,l) ->
      let l' = List.map convert_to_term l in
      { t_desc = FunApp(f,l');
	t_type = snd f.f_type;
	t_occ = Terms.new_occ(); 
	t_max_occ = 0;
	t_loc = Parsing_helper.dummy_ext;
	t_incompatible = find_map l';
	t_facts = find_facts l' }
  | PatEqual t -> t

(* [check_assign1 cur_array proba_info new_charac_args_opt new_depend_args_opt vars_to_add tmp_bad_dep st pat] 
   is called to analyze the pattern [pat] of an assignment 
   when the assigned term characterizes [b0].
   Returns [false] when the let is always going to take the else branch
   up to negligible probability.
   Returns [true] when the let can take both branches
   [cur_array] is the list of current replication indices.
   [proba_info = (t1,t2,charac_type)] when 
      - [t1] is the assigned term in which useless parts have been replaced with fresh variables [?], 
      - [t2] is a term built from the pattern [pat], 
      - [charac_type] determines the type of the part of [b0] characterized by the assigned term.
   [new_charac_args_opt = Some l] when the assigned term characterizes the cell [b0[l]],
   [new_charac_args_opt = None] when the assigned term characterizes an unknown cell of [b0];
   [new_depend_args_opt = Some l] when the assigned term depends only on the cell [b0[l]] of [b0],
   [new_depend_args_opt = None] when the assigned term depends only on unknown/several cells of [b0],
   [vars_to_add] collects the variables bound by the pattern and not already in [dvar_list],
   which must therefore be added to [dvar_list], since they depend on [b0].
   [tmp_bad_dep] is set to true when there is a bad dependency except when
   the let always takes the else branch. 
   [st] is 
        - [Compos] when the assigned term is obtained from [b0] by first applying
        poly-injective functions (functions marked [compos]), then
        functions that extract a part of their argument 
        (functions marked [uniform]).
        - [Decompos] when the assigned term is obtained from [b0] by applying functions
        that extract a part of their argument (functions marked [uniform]) *)

let rec check_assign1 cur_array ((t1, t2, charac_type) as proba_info) new_charac_args_opt new_depend_args_opt vars_to_add tmp_bad_dep st = function
    PatVar b ->
      begin
	let charac_type' = 
	  if st = Decompos then CharacType b.btype else charac_type 
	in
	try 
	  let (st',(proba_info_list, charac_args_opt, depend_args_opt)) = List.assq b (!dvar_list) in
	  begin
	    match !charac_args_opt, new_charac_args_opt with
	      Some l1, Some l2 ->
		if List.for_all2 Terms.equal_terms l1 l2 then () else
		begin
		  (* SArenaming b may allow to keep explicit indices characterized by [b] *)
		  add_advice [SArenaming b];
		  dvar_list_changed := true;
		  charac_args_opt := None
		end
	    | None, _ -> ()
	    | _ -> 
		dvar_list_changed := true;
		charac_args_opt := None
	  end;
	  begin
	    match !depend_args_opt, new_depend_args_opt with
	      Some l1, Some l2 ->
		if List.for_all2 Terms.equal_terms l1 l2 then () else
		begin
		  (* SArenaming b may allow to keep explicit indices of [b0] on which [b] depends *)
		  add_advice [SArenaming b];
		  dvar_list_changed := true;
		  depend_args_opt := None
		end
	    | None, _ -> ()
	    | _ -> 
		dvar_list_changed := true;
		depend_args_opt := None
	  end;
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
	      let display_proba_info (t1', t2', charac_type'') =
		Display.display_term t1';
		print_string ", ";
		Display.display_term t2';
		print_string ", ";
		begin
		match charac_type'' with
		  CharacType t -> print_string t.tname
		| CharacTypeOfVar b -> Display.display_binder b
		end;
		print_newline()
	      in
	      print_string " Already present: ";
	      List.iter display_proba_info (!proba_info_list);
	      print_string "Adding: ";
              display_proba_info (t1, t2, charac_type');
	      *)
	      dvar_list_changed := true;
	      proba_info_list := (t1, t2, charac_type') :: (!proba_info_list)
	    end
	with Not_found ->
	  vars_to_add := (b,(st, (ref [t1, t2, charac_type'], ref new_charac_args_opt, ref new_depend_args_opt))) :: (!vars_to_add)
      end;
      true
  | (PatTuple(f,l)) as pat ->
      if st == Decompos then
	List.for_all (check_assign1 cur_array proba_info new_charac_args_opt new_depend_args_opt vars_to_add tmp_bad_dep st) l
      else
	begin
	try 
	  let t = convert_to_term pat in
	  if (depends t) || 
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
	with Not_found ->
	  tmp_bad_dep := true;
	  true
	end
  | PatEqual t ->
      if (depends t) || 
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

(* [check_assign2 to_advise tmp_bad_dep pat] is called to analyze the pattern [pat] of
   an input or of an assignment when the assigned term does not depend on [b0].
   Returns [Some(charac_type, t')] when the let is always going to take the 
   else branch up to negligible probability. [t'] is the term with which
   the collision is eliminated and [charac_type] the type of the part of 
   [t'] characterized by the value of the pattern.
   Returns [None] when the let can take both branches 
   [to_advise] collects advised game transformations to avoid bad dependencies.
   [tmp_bad_dep] is set to true when there is a bad dependency except when
   the let always takes the else branch. *)

let rec check_assign2 to_advise tmp_bad_dep = function
    PatVar b ->
      if List.exists (fun (b',_) -> b == b') (!dvar_list) then
	begin
	  to_advise := Terms.add_eq (SArenaming b) (!to_advise);
	  tmp_bad_dep := true
	end;
      None
  | PatTuple(f,l) ->
      begin
        match check_assign2_list to_advise tmp_bad_dep l with
	  None -> None
	| Some(charac_type, l') ->
	    Some (charac_type, Terms.build_term_type (snd f.f_type) (FunApp(f,l')))
      end
  | PatEqual t ->
      match find_compos_list t with
	Some (status, charac_type,t',_) when Proba.is_large_term t ->
	  Some(charac_type, t')
      |	_ ->
	begin
	  if depends t then
	    tmp_bad_dep := true;
	  None
	end

and check_assign2_list to_advise tmp_bad_dep = function
    [] -> None
  | (a::l) ->
      match check_assign2 to_advise tmp_bad_dep a with
	None -> 
	  begin
	    match check_assign2_list to_advise tmp_bad_dep l with
	      None -> None
	    | Some(charac_type, l') -> Some(charac_type, (any_term_pat a)::l')
	  end
      |	Some(charac_type, a') -> Some(charac_type, a'::(List.map any_term_pat l))


(* [check_depend_process cur_array p] performs the dependency analysis 
   by scanning the process [p]. 
   It returns a simplified process when it succeeds,
   and raises [BadDep] when it fails.
   [cur_array] is the list of current replication indices. *)

let rec check_depend_process cur_array p' =
  match p'.i_desc with
    Nil -> Terms.iproc_from_desc Nil
  | Par(p1,p2) -> 
      let p1' = check_depend_process cur_array p1 in
      let p2' = check_depend_process cur_array p2 in
      Terms.iproc_from_desc (Par(p1',p2'))
  | Repl(b,p) -> 
      Terms.iproc_from_desc (Repl(b,check_depend_process (b::cur_array) p))
  | Input((c,tl),pat,p) -> 
      List.iter (fun t ->  
	if depends t then
	  begin
	    print_string ("At " ^ (string_of_int t.t_occ) ^ ", index of input channel ");
	    Display.display_term t;
	    print_string (" depends on " ^ (Display.binder_to_string (!main_var)) ^ ".\n");
	    raise BadDep
	  end
	    ) tl;
      let tmp_bad_dep = ref false in
      let to_advise = ref [] in
      match check_assign2 to_advise tmp_bad_dep pat with
	Some(charac_type, t1) -> 
	  (* The pattern matching of this input always fails *)
          (* Create a dummy variable for the input message *)
	  let b = Terms.create_binder "dummy_input" (Terms.new_vname())
	      (Terms.term_from_pat pat).t_type
	      cur_array
	  in
	  let t2 = Terms.term_from_binder b in
	  add_collisions_for_current_check_dependency (cur_array, [], p'.i_facts) (t1, t2, charac_type);
	  local_changed := true;
	  Terms.iproc_from_desc (Input((c, tl), PatVar b, Terms.oproc_from_desc Yield))
      |	None ->
	begin
	  if (!tmp_bad_dep) then
	    begin
	      if (!to_advise) != [] then
		add_advice (!to_advise);
	      print_string ("At " ^ (string_of_int p'.i_occ) ^ ", pattern of input ");
	      Display.display_pattern pat;
	      print_string (" depends on " ^ (Display.binder_to_string (!main_var)) ^ " but does not characterize a part of it.\n");
	      raise BadDep
	    end;
	  add_defined_pat pat;
	  Terms.iproc_from_desc (Input((c,tl), pat, check_depend_oprocess cur_array p))
	end

and check_depend_oprocess cur_array p = 
  match p.p_desc with
    Yield -> Terms.oproc_from_desc Yield
  | EventAbort f -> Terms.oproc_from_desc (EventAbort f)
  | Restr(b,p) -> 
      add_defined b;
      Terms.oproc_from_desc (Restr(b, check_depend_oprocess cur_array p))
  | Test(t,p1,p2) -> 
      begin
	match almost_indep_test cur_array t with
	  BothDepB -> raise BadDep
	| BothIndepB t' -> 
	    if not (Terms.equal_terms t t') then
	      defined_condition_update_needed := true;
	    let p1' = check_depend_oprocess cur_array p1 in
	    let p2' = check_depend_oprocess cur_array p2 in
	    Terms.oproc_from_desc (Test(t', p1',p2'))
	| OnlyThen -> 
	    local_changed := true;
	    check_depend_oprocess cur_array p1
	| OnlyElse -> 
	    local_changed := true;
	    check_depend_oprocess cur_array p2
      end
  | Find(l0,p2,find_info) ->
      let always_then = ref false in
      let check_br (b,l) = 
	List.iter (fun t -> 
	  if depends t then
	    begin
	      print_string ("At " ^ (string_of_int t.t_occ) ^ ", index of defined condition ");
	      Display.display_term t;
	      print_string (" depends on " ^ (Display.binder_to_string (!main_var)) ^ ".\n");
	      raise BadDep
	    end) l
      in
      let l0' = ref [] in
      List.iter (fun (bl,def_list,t,p1) ->
	if not (List.for_all defined_br def_list) then
	  local_changed := true
	else
	  begin
	    List.iter check_br def_list;
	    let bl' = List.map snd bl in
	    (* Compute the probability that the test fails.*)
            match almost_indep_test (bl' @ cur_array) t with
	      BothDepB -> raise BadDep
	    | OnlyThen ->
		List.iter (fun (b,_) -> add_defined b) bl;
		if def_list == [] then always_then := true;
		let defined_condition_update_needed_tmp = !defined_condition_update_needed in
		defined_condition_update_needed := false;
		let p1' = check_depend_oprocess cur_array p1 in
		let def_list' = 
		  if !defined_condition_update_needed then
		    let already_defined = Facts.get_def_vars_at p.p_facts in
		    let newly_defined = Facts.def_vars_from_defined (Facts.get_node p.p_facts) def_list in
		    Facts.update_def_list_process already_defined newly_defined bl def_list t p1'
		  else
		    def_list
		in
		defined_condition_update_needed := 
		   defined_condition_update_needed_tmp || (!defined_condition_update_needed);
		l0' := (bl, def_list', t, p1') :: (!l0')
	    | BothIndepB t' ->
		List.iter (fun (b,_) -> add_defined b) bl;
		let defined_condition_update_needed_tmp = !defined_condition_update_needed in
		defined_condition_update_needed := not (Terms.equal_terms t t');
		let p1' = check_depend_oprocess cur_array p1 in
		let def_list' = 
		  if !defined_condition_update_needed then
		    let already_defined = Facts.get_def_vars_at p.p_facts in
		    let newly_defined = Facts.def_vars_from_defined (Facts.get_node p.p_facts) def_list in
		    Facts.update_def_list_process already_defined newly_defined bl def_list t' p1'
		  else
		    def_list
		in
		defined_condition_update_needed := 
		   defined_condition_update_needed_tmp || (!defined_condition_update_needed);
		l0' := (bl, def_list', t', p1') :: (!l0')
	    | OnlyElse -> 
		local_changed := true
	  end) l0;
      if !always_then then
	begin
	  local_changed := true;
	  Terms.oproc_from_desc (Find(List.rev (!l0'), Terms.oproc_from_desc Yield, find_info))
	end
      else
	Terms.oproc_from_desc (Find(List.rev (!l0'), check_depend_oprocess cur_array p2, find_info))
  | Output((c,tl),t2,p) ->
      List.iter (fun t ->
	if depends t then
	begin
	  print_string ("At " ^ (string_of_int t.t_occ) ^ ", index of output channel ");
	  Display.display_term t;
	  print_string (" depends on " ^ (Display.binder_to_string (!main_var)) ^ ".\n");
	  raise BadDep
	end) tl;
      if depends t2 then
	begin
	  print_string ("At " ^ (string_of_int t2.t_occ) ^ ", output message ");
	  Display.display_term t2;
	  print_string (" depends on " ^ (Display.binder_to_string (!main_var)) ^ ".\n");
	  raise BadDep
	end;
      Terms.oproc_from_desc (Output((c,tl),t2, check_depend_process cur_array p))
  | Let(pat,t,p1,p2) ->
      begin
	match find_compos_list t with
	  Some (st, charac_type,t',charac_args_opt) ->
	    begin
	      let vars_to_add = ref [] in
	      let tmp_bad_dep = ref false in
	      let collect_bargs = ref [] in
	      let depend_args_opt =
		try
		  get_dep_indices collect_bargs t;
		  match !collect_bargs with
		    [l] -> Some l (* [t] depends only on [b0[l]] *)
		  | [] -> Parsing_helper.internal_error "What?!? t characterizes b0 but it does not depend on b0!"
		  | _ -> None
		with Depends -> None
	      in
	      if check_assign1 cur_array (t', Terms.term_from_pat pat, charac_type) charac_args_opt depend_args_opt vars_to_add tmp_bad_dep st pat then
		begin
		  if (!tmp_bad_dep) || (match pat with PatVar _ -> false | _ -> true) then 
		    begin
		      print_string ("At " ^ (string_of_int p.p_occ) ^ ", the assignment ");
		      Display.display_pattern pat;
		      print_string " = ";
		      Display.display_term t;
		      print_string " introduces a bad dependency:\nthe term ";
		      Display.display_term t;
		      print_string (" characterizes a part of " ^ (Display.binder_to_string (!main_var)) ^ " but the pattern ");
		      Display.display_pattern pat;
		      print_string " is not a variable and does not allow me to show that the assignment always fails.\n"; 
		      raise BadDep
		    end;
		  List.iter (function ((b,_) as b_st) ->
                    (*print_string "Adding ";
                      Display.display_binder b0;
                      print_newline();*)
		    if not (Terms.is_assign b) then
		      begin
			print_string ("At " ^ (string_of_int p.p_occ) ^ ", the variable " ^ (Display.binder_to_string b) ^ " depends on "  ^ (Display.binder_to_string (!main_var)) ^ " but is also defined by constructs other than assignments.\n");
			raise BadDep
		      end;
		    dvar_list_changed := true;
		    dvar_list := b_st :: (!dvar_list)) (!vars_to_add);
		  add_defined_pat pat;
		  let p1' = check_depend_oprocess cur_array p1 in
		  let p2' = check_depend_oprocess cur_array p2 in
		  Terms.oproc_from_desc (Let(pat, t, p1', p2'))
		end
	      else
		begin
		  local_changed := true;
		  check_depend_oprocess cur_array p2
		end
	    end
	| None ->
	    if depends t then
	      begin
		print_string ("At " ^ (string_of_int t.t_occ) ^ ", the term ");
		Display.display_term t;
		print_string (" depends on " ^ (Display.binder_to_string (!main_var)) ^ " but does not characterize a part of it.\n");
		raise BadDep
	      end
	    else
	      begin
		let to_advise = ref [] in
		let tmp_bad_dep = ref false in
		match check_assign2 to_advise tmp_bad_dep pat with
		  Some(charac_type, t1) ->
		    (* add probability *)
		    add_collisions_for_current_check_dependency (cur_array, [], p.p_facts) (t1, t, charac_type);
		    local_changed := true;
		    check_depend_oprocess cur_array p2
		| None ->
		  begin
		    if (!tmp_bad_dep) then
		      begin
			if (!to_advise) != [] then
			  add_advice (!to_advise);
			print_string ("At " ^ (string_of_int p.p_occ) ^ ", pattern of assignment ");
			Display.display_pattern pat;
			print_string (" depends on " ^ (Display.binder_to_string (!main_var)) ^ " but does not characterize a part of it.\n");
			raise BadDep
		      end;
		    add_defined_pat pat;
		    let p1' = check_depend_oprocess cur_array p1 in
		    let p2' = check_depend_oprocess cur_array p2 in
		    Terms.oproc_from_desc (Let(pat, t, p1', p2'))
		  end
	      end
      end
  | EventP(t,p) ->
      Terms.oproc_from_desc (EventP(t, check_depend_oprocess cur_array p))
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
      
(* [check_depend_iter init_proba_state] iterates the dependency analysis:
   when the dependency analysis discovers new variables that depend on [b0],
   or new variables that may defined (so new branches of [find] may be executed),
   the dependency analysis needs to be redone. 
   [init_proba_state] contains collisions eliminated before the dependency analysis.
   The probability state is reset to this value before each iteration,
   so that the actual collisions eliminated are the ones already eliminated
   before dependency analysis, plus the ones of the final iteration of the
   dependency analysis. *)

let rec check_depend_iter ((old_proba, old_term_collisions) as init_proba_state) =
  List.iter (fun (b0, _) ->
    if Settings.occurs_in_queries b0 then
      begin
	print_string ("The variable " ^ (Display.binder_to_string b0) ^ 
		      " depends on " ^ (Display.binder_to_string (!main_var)) ^ 
		      " and occurs in a query.\n");
        raise BadDep
      end;
    ) (!dvar_list);
  Proba.restore_state old_proba;
  Simplify1.term_collisions := old_term_collisions;
  vars_charac_type :=
      List.map (fun (b, (st, (proba_info_list,_,_))) -> 
	(b, List.concat (List.map (fun (_,_,charac_type) -> 
	  get_type_from_charac [b] charac_type
	    ) (!proba_info_list)))
	  ) (!dvar_list);
  local_changed := false;
  dvar_list_changed := false;
  defvar_list_changed := false;
  defined_condition_update_needed := false;
  let proc' = check_depend_process [] (!whole_game).proc in
  if (!dvar_list_changed) || (!defvar_list_changed) then check_depend_iter init_proba_state else proc'

(* [check_all_deps b0 init_proba_state g] is the entry point for calling 
   the dependency analysis from simplification.
   [b0] is the variable on which we perform the dependency analysis.
   [init_proba_state] contains collisions eliminated by before the dependency analysis,
   in previous passes of simplification.
   [g] is the full game to analyze. *)

let check_all_deps b0 init_proba_state g =
  whole_game := g;
  main_var := b0;
  let vcounter = !Terms.vcounter in
  try
    let dummy_term = Terms.term_from_binder b0 in
    let args_opt = Some (List.map Terms.term_from_repl_index b0.args_at_creation) in
    let b0st = (b0, (Decompos, (ref [dummy_term, dummy_term, CharacType b0.btype], ref args_opt, ref args_opt))) in
    dvar_list := [b0st];
    defvar_list := [];
    let proc' = check_depend_iter init_proba_state in
    let res_game = { proc = proc'; game_number = -1; current_queries = g.current_queries } in
    if not (!local_changed) then
      begin
	print_string "The global dependency analysis succeeded but did not make any change.\n";
	raise BadDep
      end;
    (* Some cleanup to free memory *)
    dvar_list := [];
    defvar_list := [];
    vars_charac_type := [];
    Some(res_game)
  with BadDep -> 
    (* Some cleanup to free memory *)
    dvar_list := [];
    defvar_list := [];
    vars_charac_type := [];
    Terms.vcounter := vcounter; (* Forget variables when fails *)
    None

(* [main b0 coll_elim g] is the entry point for calling
   the dependency analysis alone.
   [b0] is the variable on which we perform the dependency analysis.
   [coll_elim] is a list of occurrences, types or variable names 
   for which we allow eliminating collisions even if they are not [large].
   [g] is the full game to analyze. *)

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
    let res = check_all_deps b0 (([],[]),[]) g in
    (* Transfer the local advice to the global advice in Settings.advise *)
    List.iter (fun x -> Settings.advise := Terms.add_eq x (!Settings.advise)) (!advise);
    advise := [];
    match res with
      None -> (g, [], []) 
    | Some(res_game) ->
	Settings.changed := true;
	let proba = Simplify1.final_add_proba() in
	(res_game, proba, [DGlobalDepAnal(b0,coll_elim)])
    end
