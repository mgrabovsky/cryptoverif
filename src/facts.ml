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

let filter_ifletfindres l =
  List.filter Terms.check_no_ifletfindres l

(* Display facts; for debugging *)

let display_facts (subst2, facts, elsefind) =
  print_string "Substitutions:\n";
  List.iter (fun t -> Display.display_term t; print_newline()) subst2;
  print_string "Facts:\n";
  List.iter (fun t -> Display.display_term t; print_newline()) facts;
  print_string "Elsefind:\n";
  List.iter (fun (bl, def_list, t) ->
    print_string "for all ";
    Display.display_list Display.display_repl_index bl;
    print_string "; not(defined(";
    Display.display_list (fun (b,l) -> Display.display_var b l) def_list;
    print_string ") && ";
    Display.display_term t;
    print_string ")";
    print_newline()
    ) elsefind

(* On demand substitutions 

let try_no_var (subst, facts) t =
   when t is FunApp(_), return t itself.
   when t is Var(_), try applying substitutions until t becomes FunApp(_)
   if impossible, return t itself.

   It may be necessary to apply subtitutions to strict subterms of t
   in order to be able to apply another substitution to t itself.

   Apply on demand substitution when 
   - a matching for a reduction rule meets a variable when
   it expects a function symbol
   - unification called when we have an inequality meets a 
   different variable on both sides 
   - we have a variable in a boolean formula (x && ...), ...
   - equality between a variable and a variable or a tuple
   - let (...) = x[...] substitute x

Substitutions map variables x[...] to some term.

Difficulty = avoid loops; when should I stop applying substitutions
to avoid cycles? Do not reapply the same subtitution in a term
that comes from its image term, perhaps after transformation.
The difficulty is to follow what the term becomes during these
transformations.
Possible transformations are:
   - applying another substitution
   - applying a reduction rule, which does not change variables.
So keep a mapping (occ, M -> M') of forbidden substitutions,
and update it when applying a substitution. If this substitution
transforms N into N', and occ is in N then add (occ', M -> M')
for each occ' occurrence of a variable in N'.

*)

let no_dependency_anal = fun _ _ _ -> false

(* [orient t1 t2] returns true when the equality t1 = t2
   can be oriented t1 -> t2. 
   One must not orient "t1 -> term that strictly contains t1",
   because that would immediately lead to a loop.
   Other than that, the choices are mostly heuristic.
   We try to make the content of variables explicit by orienting
   Var -> non-Var, except for variables that are large restrictions,
   because their content is defined by the restriction and we can
   use elimination of collisions when these variables are present.
   For terms that start with a function symbol, we prefer orienting
   in the direction that decreases the number of variables; if the
   number of variables is the same, we prefer the direction that 
   decreases the size.
   *)

let rec orient t1 t2 = 
  match t1.t_desc, t2.t_desc with
    (Var(b1,l1), Var(b2,l2)) when
    (not (Terms.refers_to b1 t2)) && (not (Terms.refers_to b2 t1)) &&
    (not (Terms.is_restr b1 && b1.btype.tsize >= 1)) &&
    (not (Terms.is_restr b2 && b2.btype.tsize >= 1)) ->
      (* Both orientations would be possible, try to discriminate using
         priorities *)
      b1.priority >= b2.priority
  | (Var(b,l), _) when
    (not (Terms.refers_to b t2)) && 
    (not (Terms.is_restr b && b.btype.tsize >= 1)) -> true
  | (ReplIndex b1, ReplIndex b2) -> true
  | (Var(b1,l1), Var(b2,l2)) when b1 == b2 -> 
      List.for_all2 orient l1 l2
  | (FunApp(f1,l1), FunApp(f2,l2)) when f1 == f2 ->
      List.for_all2 orient l1 l2
  | (FunApp _, FunApp _) ->
      let v_t1 = Terms.count_var t1 in
      let v_t2 = Terms.count_var t2 in
      (v_t1 > v_t2) || ((v_t1 = v_t2) && (Terms.size t1 >= Terms.size t2))
  | _ -> false

let orient_eq try_no_var t1 t2 =
  if orient t1 t2 then Some(t1,t2) else
  if orient t2 t1 then Some(t2,t1) else None

let prod_orient_eq eq_th try_no_var l1 l2 =
  match eq_th with 
  | (ACUN(prod, _) | Group(prod, _, _) | CommutGroup(prod, _, _)) -> 
      let rec find_orient t2 seen = function
	  [] -> None
	| (t::l) ->
	    match t.t_desc with
	      Var _ -> 
	        (* We have product (List.rev seen) t l = t2.
		   So t = product (inv (product (List.rev seen))) t2 (inv (product l)). *)
		let t' = Terms.make_inv_prod eq_th seen t2 l in
		if orient t t' then
		  Some (t,t')
		else 
		  find_orient t2 (t::seen) l
	    | _ -> find_orient t2 (t::seen) l
      in
      begin
      match find_orient (Terms.make_prod prod l2) [] l1 with
	None -> find_orient (Terms.make_prod prod l1) [] l2
      |	x -> x
      end
  | _ -> Parsing_helper.internal_error "Expecting a group or xor theory in Facts.prod_orient_eq"

let prod_dep_anal eq_th dep_info simp_facts l1 l2 =
  match eq_th with 
  | (ACUN(prod, _) | Group(prod, _, _) | CommutGroup(prod, _, _)) -> 
      let rec find_orient t2 seen = function
	  [] -> false
	| (t::l) ->
	        (* We have product (List.rev seen) t l = t2.
		   So t = product (inv (product (List.rev seen))) t2 (inv (product l)). *)
	    let t' = Terms.make_inv_prod eq_th seen t2 l in
	    (dep_info simp_facts t t') || (find_orient t2 (t::seen) l)
      in
      (find_orient (Terms.make_prod prod l2) [] l1) ||
      (find_orient (Terms.make_prod prod l1) [] l2)
  | _ -> Parsing_helper.internal_error "Expecting a group or xor theory in Facts.prod_dep_anal"

(* Apply reduction rules defined by statements to term t *)

(* [get_var_link]: [get_var_link t ()] returns [Some (link, allow_neut)]
   when [t] is variable that can be bound by a product of terms,
   [link] is the current contents of the link of that variable,
   [allow_neut] is true if and only if the variable may be bound to
   the neutral element (provided there is a neutral element for the
   product); it returns [None] otherwise. *)

let get_var_link restr t () = 
  match t.t_desc with
    FunApp _ -> None
  | Var(v,[]) -> 
      (* If v must be a random number, it can correspond only to 1 element of 
	 the matching list l2, so it can be handled like a FunApp term
	 by match_term. *)
      if List.memq v restr then None else Some (v.link, false (* TO DO I consider that v cannot be bound to the neutral element; it would be better to allow the user to set that *))
  | Var _ | ReplIndex _ | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ ->
      Parsing_helper.internal_error "Var with arguments, replication indices, if, find, let, new, event should not occur in match_assoc"      

let rec match_term try_no_var restr next_f t t' () = 
  let get_var_link = get_var_link restr in
  let rec match_term_rec next_f t t' () =
    Terms.auto_cleanup (fun () -> 
      match t.t_desc with
	Var (v,[]) -> 
        (* Check that types match *)
	  if t'.t_type != v.btype then
	    raise NoMatch;
	  begin
	    match v.link with
	      NoLink -> 
		if List.memq v restr then
	      (* t' must be a variable created by a restriction *)
		  begin
		    if not (t'.t_type == v.btype) then
		      raise NoMatch;
		    match t'.t_desc with
		      Var(b,l) when Terms.is_restr b -> ()
		    | _ -> raise NoMatch
		  end;
		Terms.link v (TLink t')
	    | TLink t -> 
		if not (Terms.simp_equal_terms try_no_var t t') then raise NoMatch
	  end;
	  next_f()
      | FunApp(f,l) ->
	  Terms.match_funapp match_term_rec get_var_link Terms.default_match_error try_no_var next_f t t' ()
      | Var _ | ReplIndex _ | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ ->
	  Parsing_helper.internal_error "Var with arguments, replication indices, if, find, let, new, event should not occur in match_term"
	    )
  in
  match_term_rec next_f t t' ()

let match_term_root_or_prod_subterm try_no_var restr final next_f t t' =
  match t.t_desc with
    FunApp(f,[_;_]) when f.f_eq_theories != NoEq && f.f_eq_theories != Commut ->
      (* f is a binary function with an equational theory that is
	 not commutativity -> it is a product-like function *)
      let l = Terms.simp_prod try_no_var (ref false) (Terms.simp_equal_terms try_no_var) f t in
      let l' = Terms.simp_prod try_no_var (ref false) (Terms.simp_equal_terms try_no_var) f t' in
      begin
	match f.f_eq_theories with
	  NoEq | Commut -> Parsing_helper.internal_error "Facts.match_term_root_or_prod_subterm: cases NoEq, Commut should have been eliminated"
	| AssocCommut | AssocCommutN _ | CommutGroup _ | ACUN _ ->
	    Terms.match_AC (match_term try_no_var restr) (get_var_link restr) Terms.default_match_error (fun rest () -> 
	      final (Terms.make_prod f ((next_f())::rest))) try_no_var f true l l' ()
	| Assoc | AssocN _ | Group _ -> 
	    Terms.match_assoc_subterm (match_term try_no_var restr) (get_var_link restr) (fun rest_left rest_right () ->
	      final (Terms.make_prod f (rest_left @ (next_f())::rest_right))) try_no_var f l l' ()
      end
  | _ ->
      match_term try_no_var restr (fun () -> final (next_f())) t t' ()

let reduced = ref false

let rec check_indep v = function
    [] -> []
  | v'::l ->
      let l_indep = check_indep v l in
      match v.link, v'.link with
	TLink { t_desc = Var(b,l) }, TLink { t_desc = Var(b',l') } ->
	  if b == b' then
	    (Terms.make_and_list (List.map2 Terms.make_equal l l')):: l_indep
	  else
	    l_indep
      |	_ -> Parsing_helper.internal_error "variables should be linked in check_indep"

let rec check_indep_list = function
    [] -> []
  | [v] -> []
  | (v::l) ->
      (check_indep v l) @ (check_indep_list l)

(* [apply_collisions_at_root_once reduce_rec try_no_var final t collisions] 
   applies all collisions in the list [collisions] to the root of term [t].
   It calls the function [final] on each term obtained by applying a collision.
   The function final may raise the exception [NoMatch] so that other 
   possibilities are considered.

   Statements are a particular case of collisions, so this function
   can also be applied with a list of statements in [collisions].

   [reduce_rec f t] must simplify the term [t] knowing the fact [f] 
   in addition to the already known facts. It sets the flag [reduced]
   when [t] has really been modified. *)

let rec apply_collisions_at_root_once reduce_rec try_no_var final t = function
    [] -> raise NoMatch
  | (restr, forall, redl, proba, redr)::other_coll ->
      try
	match_term_root_or_prod_subterm try_no_var restr final (fun () -> 
	  let t' = Terms.copy_term Terms.Links_Vars redr in
	  let l_indep = check_indep_list restr in
	  let redl' = Terms.copy_term Terms.Links_Vars redl in
	  let restr_map = 
	    List.map (fun restr1 ->
	      match restr1.link with
		TLink trestr -> (restr1,trestr)
	      | _ -> Parsing_helper.internal_error "unexpected link in apply_red"
		    ) restr
	  in
	(* Cleanup early enough, so that the links that we create in this 
	   collision do not risk to interfere with a later application of 
	   the same collision in reduce_rec. *)
	  Terms.cleanup();
	  let t'' =
	    if l_indep == [] then
		(* All restrictions are always independent, nothing to add *)
	      t' 
	    else
	      begin
		if not (Terms.is_false redr) then
	          (* I can test conditions that make restrictions independent only
		     when the result "redr" is false *)
		  raise NoMatch;
	          (* When redr is false, the result "If restrictions
		     independent then redr else t" is equal to
		     "(restrictions not independent) and t" which we
		     simplify.  We keep the transformed value only
		     when t has been reduced, because otherwise we
		     might enter a loop (applying the collision to t
		     over and over again). *)
		Terms.make_or_list 
		  (List.map (fun f ->
		    let reduced_tmp = !reduced in
		    reduced := false;
		    let t1 = reduce_rec f t in
		    if not (!reduced) then 
		      begin 
			reduced := reduced_tmp; 
			raise NoMatch 
		      end;
		    reduced := reduced_tmp;
		    Terms.make_and f t1
		      ) l_indep)
	      end
	  in
	  if proba != Zero then
	    begin
              (* Instead of storing the term t, I store the term obtained 
                 after the applications of try_no_var in match_term,
                 obtained by (Terms.copy_term redl) *)
	      if not (Proba.add_proba_red redl' t' proba restr_map) then
		raise NoMatch
	    end;
	  t''
	    ) redl t
      with NoMatch ->
	Terms.cleanup();
	apply_collisions_at_root_once reduce_rec try_no_var final t other_coll


let reduce_rec_impossible t = assert false

let apply_statements_at_root_once try_no_var t =
  match t.t_desc with
    FunApp(f,_) ->
      begin
	try 
	  apply_collisions_at_root_once reduce_rec_impossible try_no_var (fun t' -> reduced := true; t') t f.f_statements 
	with NoMatch -> t
      end
  | _ -> t

let apply_statements_and_collisions_at_root_once reduce_rec try_no_var t =
  match t.t_desc with
    FunApp(f,_) ->
      begin
	try 
	  apply_collisions_at_root_once reduce_rec_impossible try_no_var (fun t' -> reduced := true; t') t f.f_statements 
	with NoMatch ->
	  try 
	    apply_collisions_at_root_once reduce_rec try_no_var (fun t' -> reduced := true; t') t f.f_collisions 
	  with NoMatch -> t
      end
  | _ -> t

(* [apply_simplif_subterms_once simplif_root_or_prod_subterm try_no_var t] 
   applies the simplification specified by [simplif_root_or_prod_subterm] 
   to all subterms of [t].

   [simplif_root_or_prod_subterm: term -> term] should simplify only the root
   of the term, or when the term is a product, simplify subproducts,
   but not smaller subterms. When the simplification succeeds, it sets [reduced]
   to true and returns the simplified term. When the simplification fails,
   it returns the initial term and leaves [reduced] unchanged. *)

let rec first_inv inv = function
    [] -> ([], [])
  | (a::l) as x -> 
      match a.t_desc with
	FunApp(f,[t]) when f == inv -> 
	  let (invl, rest) = first_inv inv l in
	  (t::invl, rest)
      |	_ -> 
	  ([], x)

let apply_simplif_subterms_once simplif_root_or_prod_subterm try_no_var t = 
  let rec simplif_rec t =
  match t.t_desc with
    FunApp(f, [_;_]) when f.f_eq_theories != NoEq && f.f_eq_theories != Commut ->
      (* f is a binary function with an equational theory that is
	 not commutativity -> it is a product-like function *)
      let t' = simplif_root_or_prod_subterm t in
      if !reduced then t' else 
      (* We apply the statements only to subterms that are not products by f.
	 Subterms that are products by f are already handled above
	 using [match_term_root_or_prod_subterm]. *)
      let l = Terms.simp_prod try_no_var (ref false) (Terms.simp_equal_terms try_no_var) f t in
      Terms.make_prod f (List.map simplif_rec l)
  | FunApp(f, ([t1;t2] as l)) when f.f_cat == Equal || f.f_cat == Diff ->
      let t' = simplif_root_or_prod_subterm t in
      if !reduced then t' else 
      begin
	match Terms.get_prod_list try_no_var l with
	  ACUN(xor, neut) ->
	    let t' = Terms.app xor [t1;t2] in
	    let t'' = simplif_rec t' in
	    if !reduced then 
	      begin
		match t''.t_desc with
		  FunApp(xor', [t1';t2']) when xor' == xor ->
		    Terms.build_term2 t (FunApp(f, [t1';t2']))
		| _ -> 
		    Terms.build_term2 t (FunApp(f, [t'';Terms.app neut []]))
	      end
	    else
	      t
	| CommutGroup(prod, inv, neut) -> 
	    let rebuild_term t'' = 
	      (* returns a term equal to [f(t'', neut)] *)
	      let l = Terms.simp_prod try_no_var (ref false) (Terms.simp_equal_terms try_no_var) prod t'' in
	      let linv, lno_inv = List.partition (Terms.is_fun inv) l in
	      let linv_removed = List.map (function { t_desc = FunApp(f,[t]) } when f == inv -> t | _ -> assert false) linv in
	      Terms.build_term2 t (FunApp(f, [ Terms.make_prod prod lno_inv; 
					       Terms.make_prod prod linv_removed ]))
	    in	      
	    let t' = Terms.app prod [t1; Terms.app inv [t2]] in
	    let t'' = simplif_rec t' in
	    if !reduced then
	      rebuild_term t''
	    else
	      let t' = Terms.app prod [t2; Terms.app inv [t1]] in
	      (* No need to try subterms of t' inside elements of the product,
		 since they have already been tried above *)
	      let t'' = simplif_root_or_prod_subterm t' in
	      if !reduced then
		rebuild_term t''
	      else
		t
	| Group(prod, inv, neut) ->
	    let rebuild_term t'' =
	      (* returns a term equal to [f(t'', neut)] *)
	      let l = Terms.simp_prod try_no_var (ref false) (Terms.simp_equal_terms try_no_var) prod t'' in
	      let (inv_first, rest) = first_inv inv l in
	      let (inv_last_rev, rest_rev) = first_inv inv (List.rev rest) in
		(* if inv_first = [x1...xk], inv_last_rev = [y1...yl],
		   List.rev rest_rev = [z1...zm]
		   then the term we want to rewrite is
		   x1^-1...xk^-1.z1...zm.yl^-1...y1^-1 = neut
		   which is equal to
		   z1...zm = xk...x1.y1...yl *)
	      Terms.build_term2 t (FunApp(f, [ Terms.make_prod prod (List.rev rest_rev) ; 
					       Terms.make_prod prod (List.rev_append inv_first inv_last_rev)]))
	    in
	    let l1 = Terms.simp_prod try_no_var (ref false) (Terms.simp_equal_terms try_no_var) prod (Terms.app prod [t1; Terms.app inv [t2]]) in
	    let l2 = Terms.remove_inverse_ends try_no_var (ref false) (prod, inv, neut) (Terms.simp_equal_terms try_no_var) l1 in
	    let rec apply_up_to_roll seen' rest' =
	      let t0 = (Terms.make_prod prod (rest' @ (List.rev seen'))) in
	      let t'' = simplif_root_or_prod_subterm t0 in
	      if !reduced then
		rebuild_term t''
	      else
		match rest' with
		  [] -> t
		| a::rest'' -> apply_up_to_roll (a::seen') rest''
	    in
	    let t' = apply_up_to_roll [] l2 in
	    if !reduced then t' else
	    let l3 = List.rev (List.map (Terms.compute_inv try_no_var (ref false) (prod, inv, neut)) l2) in
	    let t' = apply_up_to_roll [] l3 in
	    if !reduced then t' else
	    let l1 = Terms.simp_prod try_no_var (ref false) (Terms.simp_equal_terms try_no_var) prod t1 in
	    let l2 = Terms.simp_prod try_no_var (ref false) (Terms.simp_equal_terms try_no_var) prod t2 in
	    Terms.build_term2 t (FunApp(f, [ Terms.make_prod prod (List.map simplif_rec l1);
					     Terms.make_prod prod (List.map simplif_rec l2) ]))
	| _ -> 
	    Terms.build_term2 t (FunApp(f, List.map simplif_rec l))
      end
  | FunApp(f, l) ->
      let t' = simplif_root_or_prod_subterm t in
      if !reduced then t' else 
      Terms.build_term2 t (FunApp(f, List.map simplif_rec l))
  | _ -> t
  in
  simplif_rec t

(* For debugging: replace Terms.apply_eq_reds with apply_eq_reds below.

let apply_eq_reds try_no_var reduced t =
  let t' = Terms.apply_eq_reds try_no_var reduced t in
  if !reduced then
    begin
      print_string "apply_eq_reds ";
      Display.display_term t;
      print_string " = ";
      Display.display_term t';
      print_newline()
    end;
  t'
*)

(* [apply_eq_statements_subterms_once try_no_var t] applies the equalities 
   coming from the equational theories and the equality
   statements given in the input file to all subterms of [t]. *)

let apply_eq_statements_subterms_once try_no_var t =
  let t' = Terms.apply_eq_reds try_no_var reduced t in
  if !reduced then t' else 
  apply_simplif_subterms_once (apply_statements_at_root_once try_no_var) try_no_var t

(* [apply_eq_statements_and_collisions_subterms_once reduce_rec try_no_var t] 
   applies the equalities coming from the equational theories, 
   the equality statements, and the collisions given in the input 
   file to all subterms of [t]. *)

let apply_eq_statements_and_collisions_subterms_once reduce_rec try_no_var t =
  let t' = Terms.apply_eq_reds try_no_var reduced t in
  if !reduced then t' else 
  apply_simplif_subterms_once (apply_statements_and_collisions_at_root_once reduce_rec try_no_var) try_no_var t

(* For debugging 
let apply_eq_statements_and_collisions_subterms_once reduce_rec try_no_var t =
  let t' = apply_eq_statements_and_collisions_subterms_once reduce_rec try_no_var t in
  if !reduced then
    begin
      print_string "apply_eq_statements_and_collisions_subterms_once ";
      Display.display_term t;
      print_string " = ";
      Display.display_term t';
      print_newline()
    end;
  t'
*)

(* Applying a substitution that maps x[M1,...,Mn] to M' *)

let reduced_subst = ref false

let rec apply_subst1 try_no_var t tsubst =
  match tsubst.t_desc with
    FunApp(f,[redl;redr]) when f.f_cat == Equal || f.f_cat == LetEqual ->
      begin
	match t.t_desc with
	  FunApp(f,l) -> 
	    begin
	      (* When we apply the substitution to a FunApp term, we do not apply
		 it recursively to its subterms, to avoid getting more function
		 symbols than the minimum in try_no_var below. 
		 However, we may apply other substitutions to subterms, to make it
		 possible to apply tsubst at the root. This is done by
		 [Terms.simp_equal_terms try_no_var t redl].

		 It is important that [try_no_var] never sets [reduced_subst].
		 Otherwise, [apply_subst1] might set [reduced_subst] inside the call
		 to [Terms.simp_equal_terms try_no_var t redl], even though the
		 equality is false, so the caller of [apply_subst1] would wrongly
		 think that the term has been modified.
		*)
              if Terms.simp_equal_terms try_no_var t redl then 
		begin
		  reduced_subst := true;
		  redr
		end
              else
		t
            end
	| _ ->
           if Terms.equal_terms t redl then 
	     begin
	       reduced_subst := true;
	       redr
	     end
           else
             match t.t_desc with
               Var(b,l) ->
	         Terms.build_term2 t (Var(b, List.map (fun t' -> apply_subst1 try_no_var t' tsubst) l))
(*    
             | FunApp(f,l) ->
	         Terms.build_term2 t (FunApp(f, List.map (fun t' -> apply_subst1 try_no_var t' tsubst) l))
*)
             | _ -> t
      end
  | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"

let rec apply_subst_list t = function
    [] -> t
  | tsubst::rest -> 
     match tsubst.t_desc with
       FunApp(f,[redl;redr]) when f.f_cat == Equal || f.f_cat == LetEqual ->
         begin
           if Terms.equal_terms t redl then 
	     redr
           else
	     apply_subst_list t rest
         end
     | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"



(* Since the RHS of rewrite rules is already normalized,
   it is enough to apply rewrite rules once at each variable 
   symbol from the inside to the outside to normalize the term. *)

let rec normalize_var subst2 t =
  match t.t_desc with
    Var(b,l) ->
      let l' = List.map (normalize_var subst2) l in
      let t' = Terms.build_term2 t (Var(b,l')) in
      apply_subst_list t' subst2
  | ReplIndex _ -> 
      apply_subst_list t subst2
  | FunApp _ ->
      (* This property requires variables not to contain functions.
	 This is true now, but may change in the future. *)
      Display.display_term t; print_newline();
      Parsing_helper.internal_error "FunApp should not occur in normalize"
  | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ -> 
      Display.display_term t; print_newline();
      Parsing_helper.internal_error "If, find, let, and new should not occur in normalize"

let rec try_no_var (subst2, _, _) t =
  match t.t_desc with
    FunApp(f,l) -> t
  | Var _ | ReplIndex _ -> 
      normalize_var subst2 t 
  | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ -> 
      Display.display_term t; print_newline();
      Parsing_helper.internal_error "If, find, let, and new should not occur in try_no_var"

(*
The code below makes sure that terms with a function symbol
at the root are normalized by the rewrite rule.
It slows down the execution, so instead we simply use
[try_no_var] which leaves terms with a function symbol
at the root unchanged.

let rec apply_subst_list_fun try_no_var t = function
    [] -> t
  | tsubst::rest -> 
     match tsubst.t_desc with
       FunApp(f,[redl;redr]) when f.f_cat == Equal || f.f_cat == LetEqual ->
         begin
           if Terms.simp_equal_terms try_no_var t redl then 
	     redr
           else
	     apply_subst_list_fun try_no_var t rest
         end
     | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"

let normalize ((subst2, _, _) as simp_facts) t =
  match t.t_desc with
    FunApp(f,l) ->
      apply_subst_list_fun (try_no_var simp_facts) t subst2
  | Var _ | ReplIndex _ -> 
      normalize_var subst2 t 
  | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ -> 
      Display.display_term t; print_newline();
      Parsing_helper.internal_error "If, find, let, and new should not occur in try_no_var"
  *)
let normalize = try_no_var

(* [apply_reds simp_facts t] applies all equalities coming from the
   equational theories, equality statements, and collisions given in
   the input file to all subterms of the term [t], taking into account
   the equalities in [simp_facts] to enable their application.
   Application is repeated until a fixpoint is reached. *)

let rec apply_reds simp_facts t =
  reduced := false;
  let t' = apply_eq_statements_and_collisions_subterms_once (reduce_rec simp_facts) (try_no_var simp_facts) t in
  if !reduced then 
    apply_reds simp_facts t' 
  else
    t

(* [apply_sub1 simp_facts t link] tries to reduce the term [t]
   using the rewrite rule [link]. 
   It uses [simp_facts] to transform functional subterms of [t]
   to apply the rewrite rule [link]. When the reduction succeeds,
   it returns (true, reduced_term); otherwise, it returns (false, t). *)

and apply_sub1 simp_facts t link = 
  reduced_subst := false;
  let t1 = apply_subst1 (try_no_var simp_facts) t link in
  (!reduced_subst, t1)

(* [apply_eq_st_coll1 simp_facts t] applies all equalities coming from the
   equational theories, equality statements, and collisions given in
   the input file to all subterms of the term [t], taking into account
   the equalities in [simp_facts] to enable their application.
   At most one reduction is done. When the reduction succeeds,
   it returns (true, reduced_term); otherwise, it returns (false, t). *)

and apply_eq_st_coll1 simp_facts t =
  match t.t_desc with
    Var _ | ReplIndex _ ->
      (false, t)
  | FunApp _ ->
      reduced := false;
      let t' = apply_eq_statements_and_collisions_subterms_once (reduce_rec simp_facts) (try_no_var simp_facts) t in
      (!reduced, t')
  | _ -> Parsing_helper.internal_error "If/let/find/new not allowed in apply_eq_st_coll1"

(* [reduce_rec simp_facts f t] simplifies the term [t] knowing the fact [f] 
   in addition to the already known facts [simp_facts]. It sets the flag [reduced]
   when [t] has really been modified. *)

and reduce_rec simp_facts f t = 
  Terms.auto_cleanup (fun () ->
    let simp_facts' = simplif_add no_dependency_anal simp_facts f in
    apply_eq_statements_subterms_once (try_no_var simp_facts') t)   

(* Replaces each occurence of t in fact with true *)
and replace_with_true modified t fact =
  if (fact.t_type = Settings.t_bool) && (not (Terms.is_true fact)) && (Terms.equal_terms t fact) then
    begin
      modified := true;
      Terms.make_true ()
    end
  else
    Terms.build_term2 fact 
      (match fact.t_desc with
	| Var (b,tl) -> Var (b,tl)
	| FunApp (f, l) -> FunApp (f, List.map (replace_with_true modified t) l)
	| ReplIndex b -> ReplIndex b
	| _ ->
	    Parsing_helper.internal_error "Only Var and FunApp should occur in facts in replace_with_true")
      (* ReplIndex can occur here because replication indices can occur as arguments of functions in events *)

(* Simplify existing facts by knowing that the new term t is true, and then simplify the term t by knowing the facts are true *)
and simplify_facts dep_info (subst2,facts,elsefind) t =
  let mod_facts = ref [] in
  let not_mod_facts = ref [] in
  List.iter
    (fun t' -> 
      let m = ref false in
      let t''=replace_with_true m t t' in
      if !m then 
	mod_facts := t'' :: (!mod_facts)
      else
	not_mod_facts := t'' :: (!not_mod_facts)
    )
    facts;
  let m = ref false in
  let t' = List.fold_left (fun nt f -> replace_with_true m f nt) t ((!mod_facts)@(!not_mod_facts)) in
  (* not(true) is not simplified in add_fact, simplify it here *)
  let t' = 
    if !m then 
      apply_reds (subst2,(!not_mod_facts),elsefind) t'
    else
      t'
  in  
  t',simplif_add_list dep_info (subst2,(!not_mod_facts),elsefind) (!mod_facts) 

(* Add a fact to a set of true facts, and simplify it *)

and add_fact dep_info simp_facts fact =
  if (!Settings.debug_simplif_add_facts) then
    begin
      print_string "Adding "; Display.display_term fact; print_newline()
    end;
  let fact' = try_no_var simp_facts fact in
  let fact',simp_facts = simplify_facts dep_info simp_facts fact' in
  let (subst2,facts,elsefind)=simp_facts in
  match fact'.t_desc with
    FunApp(f,[t1;t2]) when f.f_cat == LetEqual ->
      begin
	match t1.t_desc with
	  Var(b,l) -> 
	    let t1' = Terms.build_term2 t1 (Var(b, List.map (try_no_var simp_facts) l))
	    in
	    let t2' = normalize simp_facts t2 in
	    let rec try_red_t1 = function
		[] -> (* Could not reduce t1' *)
		  subst_simplify2 dep_info simp_facts (Terms.make_let_equal t1' t2')
	      | { t_desc = FunApp(f'',[t1'';t2''])}::l when f''.f_cat == LetEqual ->
		  if Terms.equal_terms t1'' t1' then 
		    simplif_add dep_info simp_facts (Terms.make_equal t2' t2'')
		  else
		    try_red_t1 l
	      | _::l -> try_red_t1 l
	    in
	    try_red_t1 subst2
	| _ -> 
	    Parsing_helper.internal_error "LetEqual terms should have a variable in the left-hand side"
      end
  | FunApp(f,[t1;t2]) when f.f_cat == Equal ->
      let t1' = normalize simp_facts t1 in
      let t2' = normalize simp_facts t2 in
      begin
	match 
	  (match Terms.get_prod Terms.try_no_var_id t1' with 
	    NoEq -> Terms.get_prod Terms.try_no_var_id t2'
	  | x -> x)
          (* try_no_var has always been applied to t1' and t2' before, 
	     so I don't need to reapply it, I can use the identity instead *)
	with
	  NoEq ->
	    begin
	      match (t1'.t_desc, t2'.t_desc) with
		(FunApp(f1,l1), FunApp(f2,l2)) when
		f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
		  raise Contradiction
	      | (FunApp(f1,l1), FunApp(f2,l2)) when
		(f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
		  simplif_add_list dep_info simp_facts (List.map2 Terms.make_equal l1 l2)
	      | (Var(b1,l1), Var(b2,l2)) when
		(Terms.is_restr b1) &&
		(Proba.is_large_term t1'  || Proba.is_large_term t2') && (b1 == b2) &&
		(Proba.add_elim_collisions b1 b1) ->
		  simplif_add_list dep_info simp_facts (List.map2 Terms.make_equal l1 l2)
	      | (Var(b1,l1), Var(b2,l2)) when
		(Terms.is_restr b1) && (Terms.is_restr b2) &&
		(Proba.is_large_term t1' || Proba.is_large_term t2') &&
		(b1 != b2) && (Proba.add_elim_collisions b1 b2)->
		  raise Contradiction
	      | (_,_) when dep_info simp_facts t1' t2' ->
		  raise Contradiction
	      | (FunApp(f1,[]), FunApp(f2,[]) ) when
		f1 != f2 && (!Settings.diff_constants) ->
		  raise Contradiction
	          (* Different constants are different *)
              | (_, _) -> 
		  match orient_eq (try_no_var simp_facts) t1' t2' with
		    Some(t1'',t2'') -> 
		      subst_simplify2 dep_info simp_facts (Terms.make_equal t1'' t2'')
		  | None ->
		      (subst2, fact'::facts, elsefind)
	    end
	| (ACUN(prod, neut) | Group(prod, _, neut) | CommutGroup(prod, _, neut)) as eq_th -> 
	    begin
	      let l1 = Terms.simp_prod (try_no_var simp_facts) (ref false) (Terms.simp_equal_terms (try_no_var simp_facts)) prod t1' in
	      let l2 = Terms.simp_prod (try_no_var simp_facts) (ref false) (Terms.simp_equal_terms (try_no_var simp_facts)) prod t2' in
	      let l1' = List.map (normalize simp_facts) l1 in
	      let l2' = List.map (normalize simp_facts) l2 in
	      (* The argument of add_fact has always been simplified by Terms.apply_eq_reds 
		 So a xor appears only when there are at least 3 factors in total.
		 A commutative group product appears either when there are at least 3 factors,
		 or two factors on the same side of the equality without inverse.
		 A non-commutative group product may appear with two factors on one side and
		 none on the other, when there is no inverse.
		 In all cases, the simplifications FunApp/FunApp or Var/Var cannot be applied,
		 so we just try to apply dependency analysis, and orient the equation when it fails. *)
	      if prod_dep_anal eq_th dep_info simp_facts l1' l2' then
		raise Contradiction
	      else
		match prod_orient_eq eq_th (try_no_var simp_facts) l1' l2' with
		  Some(t1'',t2'') -> 
		    subst_simplify2 dep_info simp_facts (Terms.make_equal t1'' t2'')
		| None ->
		    (subst2, fact'::facts, elsefind)
	    end
	| _ -> Parsing_helper.internal_error "Expecting a group or xor theory in Facts.add_fact"
      end
  | FunApp(f,[t1;t2]) when f.f_cat == ForAllDiff ->
      let t1' = try_no_var simp_facts t1 in
      let t2' = try_no_var simp_facts t2 in
      begin
      match (t1'.t_desc, t2'.t_desc) with
	(FunApp(f1,l1), FunApp(f2,l2)) when
	(f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	  let vars = ref [] in
	  if List.for_all (Terms.single_occ_gvar vars) l1 && List.for_all (Terms.single_occ_gvar vars) l2 then
	    simplif_add dep_info simp_facts (Terms.make_or_list (List.map2 Terms.make_for_all_diff l1 l2))
	  else
	    (subst2, fact'::facts, elsefind)
      | _ -> (subst2, fact'::facts, elsefind)
      end
  | FunApp(f,[t1;t2]) when f == Settings.f_and ->
      simplif_add dep_info (add_fact dep_info simp_facts t1) t2
  | _ -> 
      if Terms.is_false fact' then raise Contradiction else
      if Terms.is_true fact' then simp_facts else
      let facts' = if List.exists (Terms.equal_terms fact') facts then facts else fact'::facts in
      (subst2, facts', elsefind)

and subst_simplify2 dep_info (subst2, facts, elsefind) link =
  if (match link.t_desc with
    FunApp(f, [t;t']) when f.f_cat == Equal || f.f_cat == LetEqual ->
      Terms.equal_terms t t'
  | _ -> false) then
    (* The newly added substitution link is the identity, just ignore it *)
    (subst2, facts, elsefind)
  else
  (* Reduce the equalities in [subst2] using the new [link] *)
  let subst2'' = ref [] in
  let rhs_reduced = ref [] in
  let not_subst2_facts = ref facts in
  let rec apply_eq_st = function
      [] -> ()
    | t0::rest ->
	begin
	  match t0.t_desc with
	    FunApp(f, [t;t']) when f.f_cat == Equal || f.f_cat == LetEqual ->
	      let simp_facts_tmp = ((!subst2'') @ rest, facts, elsefind) in
	      (* Reduce the LHS of the equality t = t' *)
	      let (reduced_lhs, t1) = apply_sub1 simp_facts_tmp t link in
	      (* Reduce the RHS of the equality t = t' *)
              let (reduced_rhs, t1') = apply_sub1 simp_facts_tmp t' link in
	      if reduced_lhs || reduced_rhs then
		let fact' = Terms.build_term_type Settings.t_bool (FunApp(f,[t1; t1'])) in
		if not reduced_lhs then
		  rhs_reduced := fact' :: (!rhs_reduced) 
		else	    
		  begin
		    if not (List.exists (Terms.equal_terms fact') (!not_subst2_facts)) then
		      not_subst2_facts := fact' :: (!not_subst2_facts)
		  end
	      else
		subst2'' := t0 :: (!subst2'')
	  | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"
	end;
	apply_eq_st rest
  in
  apply_eq_st subst2;
  let subst2 = !subst2'' in
  let new_rhs_reduced = !rhs_reduced in
  rhs_reduced := [];
  subst2'' := [];
  (* Reduce the equalities in [subst2] using statements and collisions 
     given in the input file, possibly using the new [link] to enable
     these reductions *)
  let rec apply_eq_st = function
      [] -> ()
    | t0::rest ->
	begin
    match t0.t_desc with
      FunApp(f, [t;t']) when f.f_cat == Equal || f.f_cat == LetEqual ->
	let simp_facts_tmp = (link :: (!subst2'') @ rest, facts, elsefind) in
	(* Reduce the LHS of the equality t = t' *)
	let (reduced_lhs, t1) = apply_eq_st_coll1 simp_facts_tmp t in
	(* Reduce the RHS of the equality t = t' *)
	let (reduced_rhs, t1') = apply_eq_st_coll1 simp_facts_tmp t' in
	if reduced_lhs || reduced_rhs then
	  let fact' = Terms.build_term_type Settings.t_bool (FunApp(f,[t1; t1'])) in
	  if not reduced_lhs then
	    rhs_reduced := fact' :: (!rhs_reduced) 
	  else	    
	    begin
	      if not (List.exists (Terms.equal_terms fact') (!not_subst2_facts)) then
		not_subst2_facts := fact' :: (!not_subst2_facts)
	    end
	else
	  subst2'' := t0 :: (!subst2'')
    | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"
	end;
	apply_eq_st rest
  in
  apply_eq_st subst2;
  let simp_facts = (link :: (!subst2''), !not_subst2_facts, elsefind) in
  (* Reduce the LHS of equalities in [new_rhs_reduced] using statements and collisions 
     given in the input file, possibly using the new [link] to enable
     these reductions *)
  List.iter (fun t0 -> 
    match t0.t_desc with
      FunApp(f, [t;t']) when f.f_cat == Equal || f.f_cat == LetEqual ->
	(* Reduce the LHS of the equality t = t' *)
	let (reduced_lhs, t1) = apply_eq_st_coll1 simp_facts t in
	if not reduced_lhs then
	  rhs_reduced := t0 :: (!rhs_reduced) 
	else	    
	  begin
	    let fact' = Terms.build_term_type Settings.t_bool (FunApp(f,[t1; t'])) in
	    if not (List.exists (Terms.equal_terms fact') (!not_subst2_facts)) then
	      not_subst2_facts := fact' :: (!not_subst2_facts)
	  end
    | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"
	  ) new_rhs_reduced;
  let (subst2_added_rhs_reduced, facts_to_add, elsefind) =
    specialized_add_list dep_info (link :: (!subst2''), !not_subst2_facts, elsefind) (!rhs_reduced)
  in
  simplif_add_list dep_info (subst2_added_rhs_reduced,[], elsefind) facts_to_add

and simplif_add dep_info simp_facts fact =
  if (!Settings.debug_simplif_add_facts) then
    begin
      print_string "simplif_add "; Display.display_term fact; 
      print_string " knowing\n"; display_facts simp_facts; print_newline();
    end;
  let fact' = apply_reds simp_facts fact in
  add_fact dep_info simp_facts fact'

and simplif_add_list dep_info simp_facts = function
    [] -> simp_facts
  | (a::l) -> simplif_add_list dep_info (simplif_add dep_info simp_facts a) l

(* The following functions are specialized to the case in which, in subst_simplify2,
   the added fact [link] reduces the RHS of an existing substitution, but not its LHS.
   These functions guarantee that the orientation of the substitution is not reversed,
   which would cause a possible non-termination. *)

and specialized_add_fact dep_info simp_facts fact =
  if (!Settings.debug_simplif_add_facts) then
    begin
      print_string "specialized_add_fact "; Display.display_term fact; print_newline()
    end;
  let (subst2,facts,elsefind)=simp_facts in
  match fact.t_desc with
    FunApp(f,[({ t_desc = Var _ } as t1);t2]) when f.f_cat == LetEqual ->
      let t2' = normalize simp_facts t2 in
      specialized_subst_simplify2 dep_info simp_facts (Terms.make_let_equal t1 t2')
  | FunApp(f,[t1;t2]) when f.f_cat == Equal ->
      let t2' = normalize simp_facts t2 in
      begin
	match (t1.t_desc, t2'.t_desc) with
	  (FunApp(f1,l1), FunApp(f2,l2)) when
	  f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
	    raise Contradiction
	| (FunApp(f1,l1), FunApp(f2,l2)) when
	  (f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	    (subst2, (List.map2 Terms.make_equal l1 l2) @ facts, elsefind)
	| (Var(b1,l1), Var(b2,l2)) when
	  (Terms.is_restr b1) &&
	  (Proba.is_large_term t1  || Proba.is_large_term t2') && (b1 == b2) &&
	  (Proba.add_elim_collisions b1 b1) ->
	    (subst2, (List.map2 Terms.make_equal l1 l2) @ facts, elsefind)
	| (Var(b1,l1), Var(b2,l2)) when
	  (Terms.is_restr b1) && (Terms.is_restr b2) &&
	  (Proba.is_large_term t1 || Proba.is_large_term t2') &&
	  (b1 != b2) && (Proba.add_elim_collisions b1 b2)->
	    raise Contradiction
	| (_,_) when dep_info simp_facts t1 t2' ->
	    raise Contradiction
	| (FunApp(f1,[]), FunApp(f2,[]) ) when
	  f1 != f2 && (!Settings.diff_constants) ->
	    raise Contradiction
	          (* Different constants are different *)
	| (_,_) -> 
	    if not (Terms.is_subterm t1 t2') then
	      specialized_subst_simplify2 dep_info simp_facts (Terms.make_equal t1 t2')
	    else
	      (subst2, fact::facts, elsefind)
      end
  | _ -> 
      Parsing_helper.internal_error "specialized_add_fact: t = t' expected"

and specialized_subst_simplify2 dep_info (subst2, facts, elsefind) link =
  if (match link.t_desc with
    FunApp(f, [t;t']) when f.f_cat == Equal || f.f_cat == LetEqual ->
      Terms.equal_terms t t'
  | _ -> false) then
    (* The newly added substitution link is the identity, just ignore it *)
    (subst2, facts, elsefind)
  else
  (* Reduce the equalities in [subst2] using the new [link].
     Only the RHS is reduced since we know that the LHS
     is already reduced *)
  let subst2'' = ref [] in
  let rhs_reduced = ref [] in
  let not_subst2_facts = ref facts in
  let rec apply_eq_st = function
      [] -> ()
    | t0::rest ->
	begin
	  match t0.t_desc with
	    FunApp(f, [t;t']) when f.f_cat == Equal || f.f_cat == LetEqual ->
	      (* Reduce the RHS of the equality t = t' *)
              let (red, t1') = apply_sub1 ((!subst2'') @ rest, facts, elsefind) t' link in
	      if red then
		let fact' = Terms.build_term_type Settings.t_bool (FunApp(f,[t; t1'])) in
		rhs_reduced := fact' :: (!rhs_reduced)
	      else
		subst2'' := t0 :: (!subst2'')
	  | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"
	end;
	apply_eq_st rest
  in
  apply_eq_st subst2;
  let subst2 = !subst2'' in
  subst2'' := [];
  (* Reduce the equalities in [subst2] using statements and collisions 
     given in the input file, possibly using the new [link] to enable
     these reductions - Only the RHS is reduced since we know that the LHS
     is already reduced *)
  let rec apply_eq_st = function
      [] -> ()
    | t0::rest ->
	begin
	match t0.t_desc with
	  FunApp(f, [t;t']) when f.f_cat == Equal || f.f_cat == LetEqual ->
	    (* Reduce the RHS of the equality t = t' *)
	    let (reduced, t1') = apply_eq_st_coll1 (link :: (!subst2'') @ rest, facts, elsefind) t' in
	    if reduced then
	      let fact' = Terms.build_term_type Settings.t_bool (FunApp(f,[t; t1'])) in
	      rhs_reduced := fact' :: (!rhs_reduced)
	    else
	      subst2'' := t0 :: (!subst2'')
	| _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"
	end;
	apply_eq_st rest
  in
  apply_eq_st subst2;
  specialized_add_list dep_info (link :: (!subst2''), !not_subst2_facts, elsefind) (!rhs_reduced)

and specialized_simplif_add dep_info simp_facts fact =
  if (!Settings.debug_simplif_add_facts) then
    begin
      print_string "specialized_simplif_add "; Display.display_term fact; 
      print_string " knowing\n"; display_facts simp_facts; print_newline();
    end;
  let fact' = match fact.t_desc with
    FunApp(f,[t;t']) -> 
      Terms.build_term_type Settings.t_bool (FunApp(f, [t;apply_reds simp_facts t']))
  | _ ->
      Parsing_helper.internal_error "specialized_add_fact: t = t' expected"
  in
  specialized_add_fact dep_info simp_facts fact'

and specialized_add_list dep_info simp_facts = function
    [] -> simp_facts
  | (a::l) -> specialized_add_list dep_info (specialized_simplif_add dep_info simp_facts a) l

(*let simplif_add dep_info s f =
  print_string "Adding "; Display.display_term f;
  print_string " to\n";
  display_facts s; 
  print_newline();
  try 
    let res = simplif_add dep_info s f in
    print_string "Addition done "; display_facts res;
    print_newline();
    res
  with Contradiction ->
    print_string "Contradiction\n\n";
    raise Contradiction

let simplif_add_list dep_info s fl =
  print_string "Adding "; Display.display_list Display.display_term fl;
  print_string " to\n";
  display_facts s; 
  print_newline();
  try
    let res = simplif_add_list dep_info s fl in
    print_string "Addition done "; display_facts res;
    print_newline();
    res
  with Contradiction ->
    print_string "Contradiction\n\n";
    raise Contradiction
*)

let simplif_add_find_cond dep_info simp_facts fact =
  match fact.t_desc with
    Var _ | FunApp _ -> simplif_add dep_info simp_facts fact
  | _ -> simp_facts


(* Compute the list of variables that must be defined at a certain
point, taking into account defined conditions of find *)

let rec check_non_nested seen_fsymb seen_binders t =
  match t.t_desc with
    Var(b,l) ->
      (not (List.memq b seen_binders)) &&
      (List.for_all (check_non_nested seen_fsymb (b::seen_binders)) l)
  | ReplIndex _ -> true
  | FunApp(f,l) ->
      (not (List.memq f seen_fsymb)) &&
      (List.for_all (check_non_nested (f::seen_fsymb) seen_binders) l)
  | _ -> 
      Display.display_term t; print_newline();
      Parsing_helper.internal_error "If, find, let, new should have been expanded"

(* Get the node from the p_facts field of a process / the t_facts field of a term *)

let get_node def_node_opt =
  match def_node_opt with
    None -> None
  | Some (_,_,n) -> Some n

(* is_reachable n n' returns true when n is reachable from n' *)
let rec is_reachable n n' =
  if n == n' then true else
  if n'.above_node == n' then false else
  is_reachable n n'.above_node

let get_def_vars_above n =
  List.map Terms.binderref_from_binder (Terms.add_def_vars_node [] n)

(* Given a node, return the variable references whose definition
   is guaranteed by defined conditions above that node. *)
let def_vars_from_node n = n.def_vars_at_def

(* Take into account variables that must be defined because a block of code
   is always executed until the next output/yield before passing control to
   another block of code *)
let get_def_vars_above2 current_node_opt n =
  let vars_above_n = Terms.add_def_vars_node [] n in
  match current_node_opt with
    Some current_node ->
      if is_reachable n current_node then
	Terms.intersect (==) 
	  (n.future_binders @ vars_above_n)
	  (Terms.add_def_vars_node [] current_node)
      else
	n.future_binders @ vars_above_n
  | None -> vars_above_n

(* Remove variables that are certainly defined from a def_list in a find.
   Variables that are defined above the find (so don't need a "defined"
   condition) are found by "get_def_vars_above def_node". 
   Variables that already have a "defined" condition above the current
   find are found by "def_node.def_vars_at_def". *)
let reduced_def_list def_node_opt def_list =
  match def_node_opt with
    Some (_, def_vars, def_node) ->
      Terms.setminus_binderref def_list (def_vars @ (get_def_vars_above def_node))
  | None -> def_list

(* More precise solution, but must not be used to remove elements
of def_list, just to test whether all elements of def_list are defined,
in which case for a "find ... defined(def_list) && M", if M is true,
the else branch can be removed. -- Useful to remove the "else" branches
generated by applying the security of a Diffie-Hellman key agreement,
for example. 
Removing useful elements of def_list breaks the code of SArename 

   [add_def_vars current_node def_vars_accu seen_refs br] adds in
   [def_vars_accu] the variables that are known to be defined when [br]
   is defined and [current_node] corresponds to the current program
   point. [seen_refs] stores the variables already seen to avoid loops.
*)

let rec add_def_vars current_node seen_refs ((b,l) as br) =
  if (List.for_all (check_non_nested [] [b]) l) &&
    (not (Terms.mem_binderref br (!seen_refs))) then
    begin
      seen_refs := br :: (!seen_refs);
      let def_vars_above_def = Terms.intersect_list (==) (List.map (get_def_vars_above2 current_node) b.def) in
      let def_vars_at_def = Terms.intersect_list Terms.equal_binderref (List.map def_vars_from_node b.def) in
      (* put links for the substitution b.args_at_creation -> l *)
      let bindex = b.args_at_creation in
      List.iter2 (fun b t -> b.ri_link <- TLink t) bindex l;
      (* add facts *)
      List.iter (fun b -> 
	Terms.add_binderref (b, List.map (fun ri -> match ri.ri_link with
	  NoLink -> Terms.term_from_repl_index ri
	| TLink t' -> t') b.args_at_creation) seen_refs
	  ) def_vars_above_def;
      (* compute arguments of recursive call *)
      let def_vars_at_def' = Terms.copy_def_list Terms.Links_RI def_vars_at_def in
      (* remove the links *)
      List.iter (fun b -> b.ri_link <- NoLink) bindex;
      (* recursive call *)
      List.iter (add_def_vars current_node seen_refs) def_vars_at_def'
    end

(* Take into account facts that must be true because a block of code
   is always executed until the next output/yield before passing control to
   another block of code *)
let true_facts_from_node current_node_opt n =
  match current_node_opt with
    Some current_node ->
      if is_reachable n current_node then
	Terms.intersect Terms.equal_terms (n.future_true_facts @ n.true_facts_at_def) current_node.true_facts_at_def
      else
	n.future_true_facts @ n.true_facts_at_def
  | None -> 
      n.true_facts_at_def

let rec add_facts current_node fact_accu seen_refs ((b,l) as br) =
  (* print_string "Is defined "; Display.display_var b l; print_newline(); *)
  if (List.for_all (check_non_nested [] [b]) l) &&
    (not (Terms.mem_binderref br (!seen_refs))) then
    begin
      seen_refs := br :: (!seen_refs);
      let true_facts_at_def = filter_ifletfindres (Terms.intersect_list Terms.equal_terms (List.map (true_facts_from_node current_node) b.def)) in
      let def_vars_at_def = Terms.intersect_list Terms.equal_binderref (List.map def_vars_from_node b.def) in
      (* put links for the substitution b.args_at_creation -> l *)
      let bindex = b.args_at_creation in
      List.iter2 (fun b t -> b.ri_link <- TLink t) bindex l;
      (* add facts *)
      List.iter (fun f -> 
        (* b.args_at_creation -> l *)
	let f = Terms.copy_term Terms.Links_RI f in
	(* print_string "Adding "; Display.display_term f; print_newline(); *)
	if not (List.exists (Terms.equal_terms f) (!fact_accu)) then
	  fact_accu := f :: (!fact_accu)
	  ) true_facts_at_def;
      (* compute arguments of recursive call *)
      let def_vars_at_def' = Terms.copy_def_list Terms.Links_RI def_vars_at_def in
      (* remove the links *)
      List.iter (fun b -> b.ri_link <- NoLink) bindex;
      (* recursive call *)
      List.iter (add_facts current_node fact_accu seen_refs) def_vars_at_def'
    end

(* [def_vars_from_defined current_node def_list] returns the variables that
   are known to be defined when the condition of a find with defined condition 
   [def_list] holds. [current_node] is the node of the find, at which [def_list]
   is tested (may be returned by [get_node]). *)

let def_vars_from_defined current_node def_list =
  let subterms = ref [] in
  List.iter (Terms.close_def_subterm subterms) def_list;
  let seen_refs = ref [] in
  List.iter (add_def_vars current_node seen_refs) (!subterms);
  !seen_refs

(* [facts_from_defined current_node def_list] returns the facts that
   are known to hold when the condition of a find with defined condition 
   [def_list] holds. [current_node] is the node of the find, at which [def_list]
   is tested (may be returned by [get_node]). *)

let facts_from_defined current_node def_list =
  let def_list_subterms = ref [] in
  List.iter (Terms.close_def_subterm def_list_subterms) def_list;
  let fact_accu = ref [] in
  let seen_refs = ref [] in
  List.iter (add_facts current_node fact_accu seen_refs) (!def_list_subterms);
  !fact_accu

(* [get_def_vars_at fact_info] returns the variables that are known
   to be defined given [fact_info]. *)

let get_def_vars_at = function
    Some (_,def_vars,n) ->
      let seen_refs = ref (get_def_vars_above n) in
      (* Note: def_vars contains n.def_vars_at_def *)
      List.iter (add_def_vars (Some n) seen_refs) def_vars;
      !seen_refs
  | None -> []

(* [get_facts_at fact_info] returns the facts that are known to hold
   given [fact_info]. *)

let get_facts_at = function
    None -> []
  | Some(true_facts, def_vars, n) ->
      let fact_accu = ref (filter_ifletfindres true_facts) in
      (* Note: def_vars contains n.def_vars_at_def *)
      List.iter (add_facts (Some n) fact_accu (ref [])) def_vars;
      !fact_accu

(* Functions useful to simplify def_list *)

let rec filter_def_list accu = function
    [] -> accu
  | (br::l) ->
      let implied_br = def_vars_from_defined None [br] in
      let accu' = Terms.setminus_binderref accu implied_br in
      let l' = Terms.setminus_binderref l implied_br in
      filter_def_list (br::accu') l'

let rec remove_subterms accu = function
    [] -> accu
  | (br::l) ->
      let subterms = ref [] in
      Terms.close_def_subterm subterms br;
      let accu' = Terms.setminus_binderref accu (!subterms) in
      let l' = Terms.setminus_binderref l (!subterms) in
      remove_subterms (br::accu') l' 

let eq_deflists dl dl' =
  (List.for_all (fun br' -> Terms.mem_binderref br' dl) dl') &&
  (List.for_all (fun br -> Terms.mem_binderref br dl') dl) 

(*****
   Show that elements of the array b at different indices are always
   different (up to negligible probability).
   This is useful for showing secrecy of a key.
 *****)


let make_indexes b =
  List.map (fun t -> 
    Terms.term_from_repl_index (Terms.new_repl_index t)) b.args_at_creation

let collect_facts accu (def,bindex,index) =
  let fact_accu = ref accu in
  let seen_refs = ref [] in
  (* add facts *)
  List.iter (fun f -> 
    let f = Terms.subst bindex index f in
    if not (List.memq f (!fact_accu)) then
      fact_accu := f :: (!fact_accu)) (filter_ifletfindres def.true_facts_at_def);
  (* recursive call *)
  List.iter (fun (b',l') ->
    add_facts None fact_accu seen_refs (b', List.map (Terms.subst bindex index) l')
      ) def.def_vars_at_def;
  (* Result *)
  !fact_accu

let rec collect_facts_list bindex index1 = function
    [] -> []
  | (d::l) ->
      let l' = collect_facts_list bindex index1 l in
      try
	(d, collect_facts [] (d,bindex,index1))::l'
      with Contradiction ->
	l'

let check_distinct b g =
  Proba.reset [] g;
  Terms.build_def_process None g.proc;
  let index1 = make_indexes b in
  let index2 = make_indexes b in
  let diff_index = Terms.make_or_list (List.map2 Terms.make_diff index1 index2) in
  let bindex = b.args_at_creation in
  let d1withfacts = collect_facts_list bindex index1 b.def in
  let d2withfacts = collect_facts_list bindex index2 b.def in
  let r = 
  List.for_all (fun (d1,d1facts) ->
    List.for_all (fun (d2,d2facts) ->
      match d1.definition, d2.definition with
	DProcess { p_desc = Restr _ }, DProcess { p_desc = Restr _} -> true
      | DProcess { p_desc = Restr _ }, 
	    (DProcess { p_desc = Let(PatVar _,{ t_desc = Var(b',l) },_,_)}
	    |DTerm { t_desc = LetE(PatVar _, { t_desc = Var(b',l) },_,_) }) ->
		if not (Terms.is_restr b') then
		  Parsing_helper.internal_error "restriction should be checked when testing secrecy";
		(b != b') || 
		(
		try
		  let eq_b = Terms.make_and_list 
		      (List.map2 Terms.make_equal index1 (List.map (Terms.subst bindex index2) l))
		  in
		  let facts1 = diff_index :: eq_b :: d1facts @ d2facts in
		  ignore (simplif_add_list no_dependency_anal ([],[],[]) facts1);
		  false
		with Contradiction -> true
		    )
      |	(DProcess { p_desc = Let(PatVar _,{ t_desc = Var(b',l) },_,_)}
        |DTerm { t_desc = LetE(PatVar _, { t_desc = Var(b',l) },_,_) }), 
		DProcess { p_desc = Restr _ } ->
	  true (* The symmetric case will be checked by the previous pattern *)
      |	(DProcess { p_desc = Let(PatVar _,{ t_desc = Var(b1',l1) },_,_)}
        |DTerm { t_desc = LetE(PatVar _, { t_desc = Var(b1',l1) },_,_) }),
	  (DProcess {p_desc = Let(PatVar _,{ t_desc = Var(b2',l2) },_,_)}
          |DTerm { t_desc = LetE(PatVar _, { t_desc = Var(b2',l2) },_,_) }) ->
		if not ((Terms.is_restr b1') && (Terms.is_restr b2')) then
		  Parsing_helper.internal_error "restriction should be checked when testing secrecy";
		(b1' != b2') || 
		(
		try
		  let eq_b = Terms.make_and_list 
		      (List.map2 Terms.make_equal 
			 (List.map (Terms.subst bindex index1) l1) 
			 (List.map (Terms.subst bindex index2) l2))
		  in
		  let facts1 = diff_index :: eq_b :: d1facts @ d2facts in
		  ignore (simplif_add_list no_dependency_anal ([],[],[]) facts1);
		  false
		with Contradiction -> true
		    )
      | _ -> 
	  Parsing_helper.internal_error "definition cases should be checked when testing secrecy"
	  ) d2withfacts
      ) d1withfacts
  in
  if r then
    (* Add probability for eliminated collisions *)
    (true, Proba.final_add_proba[])
  else
    (false, [])

        (*
        print_string "Facts for check_distinct 1:\n";
        List.iter (fun t -> Display.display_term t; print_newline()) facts1;

        print_string "Facts for check_distinct 2:\n";
        display_facts facts;
        *)


(***** Check correspondence assertions *****)

(* [get_var_link] function associated to [guess_by_matching].
   See the interface of [Terms.match_funapp] for the 
   specification of [get_var_link]. *)

let get_var_link_g t () = 
  match t.t_desc with
    FunApp _ -> None
  | Var(v,[]) -> Some (v.link, true)
  | Var _ | ReplIndex _ | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ ->
      Parsing_helper.internal_error "Var with arguments, replication indices, if, find, let, new, event should not occur in guess_by_matching"      

let rec guess_by_matching simp_facts next_f t t' () = 
  match t.t_desc with
    Var (v,[]) -> 
    (* Check that types match *)
      if t'.t_type != v.btype then
	raise NoMatch;
      begin
	match v.link with
	  NoLink -> Terms.link v (TLink t')
	| TLink t -> ()
      end;
      next_f()
  | FunApp _ ->
      Terms.match_funapp (guess_by_matching simp_facts) get_var_link_g next_f (try_no_var simp_facts) next_f t t' ()
  | Var _ | ReplIndex _ | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ ->
      Parsing_helper.internal_error "Var with arguments, replication indices, if, find, let, and new should not occur in guess_by_matching"

let guess_by_matching_same_root next_f simp_facts t t' = 
  match t.t_desc with
    Var (v,[]) -> 
      guess_by_matching simp_facts next_f t t' ()
  | FunApp(f,l) ->
      begin
	let t'' = try_no_var simp_facts t' in 
	match t''.t_desc with
	  FunApp(f',l') when f == f' ->
	    guess_by_matching simp_facts next_f t t'' ()
	| _ -> raise NoMatch
      end
  | Var _ | ReplIndex _ | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ ->
      Parsing_helper.internal_error "Var with arguments, replication indices, if, find, let, and new should not occur in guess_by_matching"

let rec collect_vars accu t =
  match t.t_desc with
    Var(b,[]) -> accu := b :: (!accu)
  | FunApp(f,l) -> List.iter (collect_vars accu) l
  | _ -> Parsing_helper.internal_error "expecting variable or function in collect_vars"

let show_fact facts fact =
  Terms.auto_cleanup (fun () ->
      try
        ignore(simplif_add no_dependency_anal facts (Terms.make_not fact));
(*	let r = simplif_add no_dependency_anal facts (Terms.make_not fact) in
	print_string "Failed to prove "; 
	Display.display_term fact;
	print_newline();
	print_string "Simplified facts: ";
	display_facts r; *)
	false
      with Contradiction ->
(*	print_string "Proved "; 
	Display.display_term fact;
	print_newline();*)
	true)


(* Try to prove injectivity for injective correspondences 
   simp_facts = facts derivable 
   injrepidxs = list of sequences of replication indexes at the injective end events
   begin_sid = sequence of replication indexes at an injective begin event

   facts', injrepidxs', begin_sid' = same thing for another way of proving
   the concerned injective begin event, with renamed variables.

   (Variables in t1/t2 do not occur in the facts. 
   Only variables in t1/t2 have links.)

   *)

let check_inj_compat (simp_facts, injrepidxs, _, begin_sid) facts' injrepidxs' begin_sid' =
  Terms.auto_cleanup (fun () ->
    try
      let facts_with_inj1 = simplif_add_list no_dependency_anal simp_facts facts' in
      (* injrepidxs \neq injrepidxs' *)
      let diff_fact = Terms.make_or_list (List.concat (List.map2 
	(List.map2 Terms.make_diff) injrepidxs injrepidxs')) in
      let facts_with_inj2 = simplif_add no_dependency_anal facts_with_inj1 diff_fact in
      (* begin_sid = begin_sid' *)
      let eq_facts = List.map2 Terms.make_equal begin_sid begin_sid' in
      let _ = simplif_add_list no_dependency_anal facts_with_inj2 eq_facts in
      raise NoMatch
    with Contradiction ->
      ())

let add_inj simp_facts injrepidxs (repl_indices, vars) fact' fact injinfo =
  match fact'.t_desc with
    FunApp(_, { t_desc = FunApp(_, begin_sid) }::_) ->
      begin
	let (subst, facts, _) = simp_facts in
	let nsimpfacts = subst @ facts in 
	List.iter (fun b -> b.ri_link <- TLink (Terms.term_from_repl_index (Terms.new_repl_index b))) repl_indices;
	List.iter (fun b -> b.link <- TLink (Terms.term_from_binder (Terms.new_binder b))) vars;
	let new_facts = List.map (Terms.copy_term Terms.Links_RI_Vars) nsimpfacts in
	let new_injrepidxs = List.map (List.map (Terms.copy_term Terms.Links_RI_Vars)) injrepidxs in
	let new_begin_sid = List.map (Terms.copy_term Terms.Links_RI_Vars) begin_sid in
	List.iter (fun b -> b.ri_link <- NoLink) repl_indices;
	List.iter (fun b -> b.link <- NoLink) vars;
(*
	print_string "Checking inj compatiblity\n";
	display_facts simp_facts;
	print_string "New facts\n";
	List.iter (fun f -> Display.display_term f; print_newline()) new_facts;
	print_string "Inj rep idxs:";
	Display.display_list (Display.display_list Display.display_term) injrepidxs;
	print_string "\nNew inj rep idxs:";
	Display.display_list (Display.display_list Display.display_term) new_injrepidxs;
	print_string "\nBegin sid:";
	Display.display_list Display.display_term begin_sid;
	print_string "\nNew begin sid:";
	Display.display_list Display.display_term new_begin_sid;
	print_string "\n\n";
*)
	check_inj_compat (simp_facts, injrepidxs, vars, begin_sid) new_facts new_injrepidxs new_begin_sid;
	try
	  let l = List.assq fact injinfo in
	  List.iter (fun lelem -> check_inj_compat lelem new_facts new_injrepidxs new_begin_sid) l;
	  (fact, (simp_facts, injrepidxs, vars, begin_sid) :: l) :: (List.filter (fun (f, _) -> f != fact) injinfo)
	with Not_found ->
	  (fact, [(simp_facts, injrepidxs, vars, begin_sid)]) ::injinfo 
      end
  | _ -> Parsing_helper.internal_error "event should have session id"

(* try to find a instance of fact in the list of facts given as
last argument *)
let rec prove_by_matching next_check simp_facts injrepidxs vars injinfo is_inj fact = function
    [] -> raise NoMatch
  | (fact'::l) ->
      let tmp_proba_state = Proba.get_current_state() in
      try
	Terms.auto_cleanup (fun () ->
          (* When I am trying to prove an event, the root symbol is
             the event symbol, and it must really be the same for
             fact and fact'. When I am trying to prove another fact,
             it is a good heuristic, since a variable can be bound
             only when at least the root symbol is the same *)
	  guess_by_matching_same_root (fun () ->
(*	    print_string "Found ";
	    Display.display_term fact';
	    print_string " as instance of ";
	    Display.display_term fact;
	    print_newline();*)
	    (* Check that all variables of fact are instantiated *)
	    let vars_fact = ref [] in
	    collect_vars vars_fact fact;
	    if not ((List.for_all (fun b -> (b.link != NoLink)) (!vars_fact)) &&
                    (* ... and that fact' is equal to fact *)
	            show_fact simp_facts (Terms.make_equal fact' (Terms.copy_term Terms.Links_Vars fact)))
	    then raise NoMatch;
	    if is_inj then 
	      next_check (add_inj simp_facts injrepidxs vars fact' fact injinfo)
	    else
	      next_check injinfo
	    ) simp_facts fact fact');
      with NoMatch -> 
	Proba.restore_state tmp_proba_state;
	prove_by_matching next_check simp_facts injrepidxs vars injinfo is_inj fact l

let rec check_term next_check ((_,facts2,_) as facts) injrepidxs vars injinfo = function
    QAnd(t,t') ->
      check_term (fun injinfo' -> check_term next_check facts injrepidxs vars injinfo' t')
	facts injrepidxs vars injinfo t
  | QOr(t,t') ->
      begin
	let tmp_proba_state = Proba.get_current_state() in
	try
	  Terms.auto_cleanup (fun () ->
	    check_term next_check facts injrepidxs vars injinfo t)
	with NoMatch ->
	  Proba.restore_state tmp_proba_state;
	  check_term next_check facts injrepidxs vars injinfo t'
      end
  | QTerm t2 ->
      begin
	(* Try to find an instance of t2 in simp_facts *)
	let tmp_proba_state = Proba.get_current_state() in
	try
	  prove_by_matching next_check facts injrepidxs vars injinfo false t2 facts2
	with NoMatch -> 
	  Proba.restore_state tmp_proba_state;
	  (* If failed, try to prove t2 by contradiction,
	     when t2 is fully instantiated *)
	  let vars_t2 = ref [] in
	  collect_vars vars_t2 t2;
	  if (List.for_all (fun b -> (b.link != NoLink)) (!vars_t2)) &&
	    (show_fact facts (Terms.copy_term Terms.Links_Vars t2))
	      then next_check injinfo else raise NoMatch
      end
  | QEvent(is_inj,t2) ->
      begin
	(* Try to find an instance of t2 in simp_facts *)
	let tmp_proba_state = Proba.get_current_state() in
	try
	  prove_by_matching next_check facts injrepidxs vars injinfo is_inj t2 facts2
	with NoMatch -> 
	  Proba.restore_state tmp_proba_state;
	  raise NoMatch
      end


(* This is a modified version of add_facts/get_facts_at to give
   advise information, to facilitate the proof of correspondences.
   I advise (SArename b) when the intersection over all definitions
   of b leads to losing events needed to prove the correspondence. *)

let intersect_list_useful_facts (is_useful, advise_ref) advice_sa_ren l =
  let inter_l = Terms.intersect_list Terms.equal_terms l in
  (* If a useful fact has been removed due to the intersection, 
     advise SA renaming the variable [advice_sa_ren], to distinguish
     cases depending on the definition of this variable. *)
  if List.exists (fun l1 -> 
    List.exists (fun f -> is_useful f && (not (List.exists (Terms.equal_terms f) inter_l))) l1) l then
    advise_ref := Terms.add_eq (SArenaming advice_sa_ren) (!advise_ref);
  inter_l

let intersect_list_useful_br seen_refs l = 
  let inter_l = Terms.intersect_list Terms.equal_binderref l in
  let missed_br = ref [] in
  List.iter (fun l1 ->
    List.iter (fun br ->
      if not (Terms.mem_binderref br seen_refs ||
              Terms.mem_binderref br inter_l) then
	Terms.add_binderref br missed_br) l1) l;
  (inter_l, !missed_br)

let rec add_facts ((is_useful, advise_ref) as is_useful_info) current_node fact_accu seen_refs ((b,l) as br) =
  (* print_string "Is defined "; Display.display_var b l; print_newline(); *)
  if (List.for_all (check_non_nested [] [b]) l) &&
    (not (Terms.mem_binderref br (!seen_refs))) then
    begin
      seen_refs := br :: (!seen_refs);
      let true_facts_at_def = 
	filter_ifletfindres (intersect_list_useful_facts is_useful_info b (List.map (true_facts_from_node current_node) b.def)) 
      in
      let (def_vars_at_def, missed_br) = intersect_list_useful_br (!seen_refs) (List.map def_vars_from_node b.def) in
      (* put links for the substitution b.args_at_creation -> l *)
      let bindex = b.args_at_creation in
      List.iter2 (fun b t -> b.ri_link <- TLink t) bindex l;
      (* add facts *)
      List.iter (fun f -> 
        (* b.args_at_creation -> l *)
	let f = Terms.copy_term Terms.Links_RI f in
	(* print_string "Adding "; Display.display_term f; print_newline(); *)
	if not (List.exists (Terms.equal_terms f) (!fact_accu)) then
	  fact_accu := f :: (!fact_accu)
	  ) true_facts_at_def;
      (* compute arguments of recursive call *)
      let def_vars_at_def' = Terms.copy_def_list Terms.Links_RI def_vars_at_def in
      (* binderrefs missed due to the intersection over definitions of b *)
      let missed_br' = Terms.copy_def_list Terms.Links_RI missed_br in
      (* remove the links *)
      List.iter (fun b -> b.ri_link <- NoLink) bindex;
      (* recursive call *)
      List.iter (add_facts is_useful_info current_node fact_accu seen_refs) def_vars_at_def';
      (* facts that would be collected thanks to the binderrefs missed due 
	 to the intersection over definitions of b *)
      let missed_facts = ref [] in
      let seen_refs_tmp = ref (!seen_refs) in
      List.iter (add_facts is_useful_info current_node missed_facts seen_refs_tmp) missed_br';
      if List.exists (fun f -> is_useful f && (not (List.exists (Terms.equal_terms f) (!fact_accu)))) (!missed_facts) then
	advise_ref := Terms.add_eq (SArenaming b) (!advise_ref)	
    end

let get_facts_at_useful_facts is_useful_info = function
    None -> []
  | Some(true_facts, def_vars, n) ->
      let fact_accu = ref (filter_ifletfindres true_facts) in
      (* Note: def_vars contains n.def_vars_at_def *)
      List.iter (add_facts is_useful_info (Some n) fact_accu (ref [])) def_vars;
      !fact_accu

let rec get_events accu = function
    QTerm _ -> accu
  | QAnd(t1, t2) | QOr(t1, t2) -> get_events (get_events accu t1) t2
  | QEvent(_,t) ->
      match t.t_desc with
	FunApp(f,_) -> f :: accu
      |	_ -> Parsing_helper.internal_error "Events should be function applications in Facts.get_events"

let check_corresp (t1,t2) g =
   Terms.auto_cleanup (fun () ->
(* Dependency collision must be deactivated, because otherwise
   it may consider the equality between t1 and t1' below as an unlikely
   collision, because t1 does not depend on variables in the process.
   That's why I use "no_dependency_anal" *)

(*  print_string "Trying to prove ";
  Display.display_query (QEventQ(t1,t2), g);*)
  Proba.reset [] g;
  let event_accu = ref [] in
  Terms.build_def_process (Some event_accu) g.proc;
  let vars_t1 = ref [] in
  List.iter (fun (_, t) -> collect_vars vars_t1 t) t1;
  let vars_t1' = List.map (fun b ->
    let rec def_node = { above_node = def_node; binders = [];
			 true_facts_at_def = []; def_vars_at_def = []; 
			 elsefind_facts_at_def = [];
			 future_binders = []; future_true_facts = [];
			 definition = DNone }
    in
    b.def <- [def_node];
    let b' = Terms.new_binder b in
    Terms.link b (TLink (Terms.term_from_binder b'));
    b') (!vars_t1)
  in
  (* A fact that is an event that occurs in [t2] is particularly
     useful, since it can allow us to prove [t2].
     We are going to advise SArename if an intersection
     removes such a fact. These pieces of advicce are stored in
     [advise_ref] *)
  let advise_ref = ref [] in
  let events_t2 = get_events [] t2 in
  let is_useful f = 
    match f.t_desc with
      FunApp(f',_) -> List.memq f' events_t2 
    | _ -> false
  in
  let collect_facts1 next_f facts injrepidxs vars (is_inj,t) =
    List.for_all (fun (t1',fact_info) ->
      match t.t_desc,t1'.t_desc with
	FunApp(f,idx::l),FunApp(f',idx'::l') ->
	  if f == f' then
	    try
	      let end_sid = 
		match idx'.t_desc with
		  FunApp(_,lsid) -> lsid
		| _ -> Parsing_helper.internal_error "Session ids should occur first in the arguments of events"
	      in
	      let bend_sid = List.map Terms.repl_index_from_term end_sid in
	      let new_bend_sid = List.map Terms.new_repl_index bend_sid in
	      let new_end_sid = List.map Terms.term_from_repl_index new_bend_sid in
	      let eq_facts = List.map2 Terms.make_equal (List.map (Terms.copy_term Terms.Links_Vars) l) (List.map (Terms.subst bend_sid new_end_sid) l') in
	      let new_facts = List.map (Terms.subst bend_sid new_end_sid) (get_facts_at_useful_facts (is_useful, advise_ref) fact_info) in
(*
              print_string "\nFound ";
              Display.display_term t1';
              print_string " with facts\n";
              List.iter (fun t -> Display.display_term t; print_newline()) (eq_facts @ new_facts);
*)
	      let facts1 = Terms.auto_cleanup (fun () -> simplif_add_list no_dependency_anal facts new_facts) in
(*            print_string "First step without contradiction\n"; *)
	      let facts' = Terms.auto_cleanup (fun () -> simplif_add_list no_dependency_anal facts1 eq_facts) in
(*            print_string "After simplification ";
              display_facts facts'; *)
	      if not is_inj then
		next_f facts' injrepidxs (new_bend_sid @ vars)
	      else
		next_f facts' (new_end_sid :: injrepidxs) (new_bend_sid @ vars)
	    with Contradiction -> 
(*            print_string "Contradiction. Proof succeeded.\n";*)
	      true
	  else 
	    true
      | _ -> Parsing_helper.internal_error "event expected in check_corresp"
	    ) (!event_accu)
  in
  let rec collect_facts_list next_f facts injrepidxs vars = function
      [] -> next_f facts injrepidxs vars
    | (a::l) -> collect_facts1 (fun facts' injrepidxs' vars' -> collect_facts_list next_f facts' injrepidxs' vars' l) facts injrepidxs vars a
  in  
  let injinfo = ref [] in
  let r =
    collect_facts_list (fun facts' injrepidxs' vars' ->
      try 
	Terms.auto_cleanup (fun () -> 
	  check_term (fun injinfo' -> injinfo := injinfo'; true) facts' injrepidxs' (vars', vars_t1') (!injinfo) t2)
      with NoMatch -> 
	false
	  ) ([],[],[]) [] [] t1
  in
  if r then
    (* Add probability for eliminated collisions *)
    (true, Proba.final_add_proba [])
  else
    begin
      if (!advise_ref) != [] then
	begin
	  print_string "User advice: to prove ";
	  Display.display_query (QEventQ(t1,t2),{game_number = 1; proc = g.proc; current_queries = []});
	  print_string ", you could try\n";
	  List.iter (fun i -> print_string "  "; Display.display_instruct i; print_newline()) (!advise_ref)
	end;
      (false, [])
    end)

(***** Simplify a term knowing some true facts *****)

let rec simplify_term_rec dep_info simp_facts t =
  let t' = try_no_var simp_facts t in
  match t'.t_desc with
    FunApp(f, [t1;t2]) when f == Settings.f_and ->
      begin
	try
          (* We simplify t2 knowing t1 (t2 is evaluated only when t1 is true) *)
	  let simp_facts2 = simplif_add dep_info simp_facts t1 in
	  let t2' = simplify_term_rec dep_info simp_facts2 t2 in
          (* we can swap the "and" to evaluate t1 before t2 *)
	  let simp_facts1 = simplif_add dep_info simp_facts t2' in
	  Terms.make_and (simplify_term_rec dep_info simp_facts1 t1) t2'
	with Contradiction -> 
	  (* Adding t1 or t2' raised a Contradiction *)
	  Terms.make_false()
      end
  | FunApp(f, [t1;t2]) when f == Settings.f_or ->
      begin
	try 
          (* We simplify t2 knowing (not t1) (t2 is evaluated only when t1 is false) *)
	  let simp_facts2 = simplif_add dep_info simp_facts (Terms.make_not t1) in
	  let t2' = simplify_term_rec dep_info simp_facts2 t2 in
          (* we can swap the "or" to evaluate t1 before t2 *)
	  let simp_facts1 = simplif_add dep_info simp_facts (Terms.make_not t2') in
	  Terms.make_or (simplify_term_rec dep_info simp_facts1 t1) t2'
	with Contradiction ->
	  (* Adding (not t1) or (not t2') raised a Contradiction, t1 or t2' is always true *)
	  Terms.make_true()
      end
  | FunApp(f, [t1;t2]) when f.f_cat == Equal ->
      let t1' = try_no_var simp_facts t1 in
      let t2' = try_no_var simp_facts t2 in
      begin
	match t1'.t_desc, t2'.t_desc with
	  (FunApp(f1,l1), FunApp(f2,l2)) when
	  (f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	    simplify_term_rec dep_info simp_facts (Terms.make_and_list (List.map2 Terms.make_equal l1 l2))
	| (Var(b1,l1), Var(b2,l2)) when
	  (Terms.is_restr b1) &&
	  (Proba.is_large_term t1' || Proba.is_large_term t2') && (b1 == b2) &&
	  (Proba.add_elim_collisions b1 b1) ->
          (* add_proba (Div(Cst 1, Card b1.btype)); * number applications *)
	    simplify_term_rec dep_info simp_facts (Terms.make_and_list (List.map2 Terms.make_equal l1 l2))
	| _ ->
	    try
	      let _ = simplif_add dep_info simp_facts t' in
	      apply_reds simp_facts t 
	    with Contradiction -> 
	      Terms.make_false()
      end
  | FunApp(f, [t1;t2]) when f.f_cat == Diff ->
      let t1' = try_no_var simp_facts t1 in
      let t2' = try_no_var simp_facts t2 in
      begin
	match t1'.t_desc, t2'.t_desc with
	  (FunApp(f1,l1), FunApp(f2,l2)) when
	  (f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	    simplify_term_rec dep_info simp_facts (Terms.make_or_list (List.map2 Terms.make_diff l1 l2))

	| (Var(b1,l1), Var(b2,l2)) when
	  (Terms.is_restr b1) &&
	  (Proba.is_large_term t1' || Proba.is_large_term t2') && (b1 == b2) &&
	  (Proba.add_elim_collisions b1 b1) ->
          (* add_proba (Div(Cst 1, Card b1.btype)); * number applications *)
	    simplify_term_rec dep_info simp_facts (Terms.make_or_list (List.map2 Terms.make_diff l1 l2))
	| _ -> 
	    try
	      let _ = simplif_add dep_info simp_facts (Terms.make_not t') in
	      apply_reds simp_facts t
	    with Contradiction -> 
	      Terms.make_true()
      end
  | _ -> apply_reds simp_facts t

let simplify_term dep_info simp_facts t = 
  let t' = apply_reds simp_facts t in
  if t'.t_type == Settings.t_bool then
    simplify_term_rec dep_info simp_facts t'
  else
    t'



(***** Show that two terms are equal (up to negligible probability) *****
       Terms.build_def_process must have been called so that t.t_facts has been filled.
       "and_facts" contains facts that are known to hold, in addition to the
       facts recorded in the process. This is useful for expressions such as
       "t1 && t": we can consider that t1 holds when we evaluate t'. 

       "and_facts" also contains facts derived by the get_elsefind_facts function
       and are true with probability and_proba.
*)

(* [apply_eq add_accu t equalities] applies the equalities of [equalities] 
   to the term [t], at the root or to the immediate subterms in case [t] is
   a product. Each equality is applied at most once.
   It calls the function [add_accu] on each obtained term. 

   [get_var_link_novar] is the [get_var_link] function used for matching
   inside [apply_eq]. It always returns [None] since nothing is considered
   as a variable in this matching: we just want equality of terms.

   [match_term_novar] is the [match_term] function used for matching
   inside [apply_eq]. It just tests equality, since nothing is considered
   as a variable in this matching.
*)
let get_var_link_novar t () = None

let match_term_novar next_f t t' () =
  if Terms.equal_terms t t' then next_f() else raise NoMatch

let apply_eq add_accu t equalities =
  List.iter (fun (left, right) ->
    match t.t_desc, left.t_desc with
      FunApp(f,[_;_]), _ when f.f_eq_theories != NoEq && f.f_eq_theories != Commut ->
      (* f is a binary function with an equational theory that is
	 not commutativity -> it is a product-like function *)
	let l = Terms.simp_prod Terms.try_no_var_id (ref false) Terms.equal_terms f t in
	let l' = Terms.simp_prod Terms.try_no_var_id (ref false) Terms.equal_terms f left in
	begin
	  match f.f_eq_theories with
	    NoEq | Commut -> Parsing_helper.internal_error "Facts.match_term_root_or_prod_subterm: cases NoEq, Commut should have been eliminated"
	  | AssocCommut | AssocCommutN _ | CommutGroup _ | ACUN _ ->
	    (* By commutativity, all possibilities will yield the same result, so we do not raise NoMatch
	       after finding a solution. *)
	      begin
		try 
		  Terms.match_AC match_term_novar get_var_link_novar Terms.default_match_error (fun rest () -> 
		    add_accu (Terms.make_prod f (right::rest))) Terms.try_no_var_id f true l l' ()
		with NoMatch -> ()
	      end
	  | Assoc | AssocN _ | Group _ -> 
	    (* Try all possibilities *)
	      begin
		try
		  Terms.match_assoc_subterm match_term_novar get_var_link_novar (fun rest_left rest_right () ->
		    add_accu (Terms.make_prod f (rest_left @ right::rest_right)); raise NoMatch) Terms.try_no_var_id f l l' ()
		with NoMatch -> ()
	      end
	end
    | _ ->
	if Terms.equal_terms t left then add_accu right
	    ) equalities

(* [apply_colls reduce_rec add_accu t colls] applies the collisions in
   [colls] to the term [t], at the root or in immediate subterms in case
   [t] is a product. Each collision is applied at most once. 
   It calls the function [add_accu] on each obtained term.
   *)

let apply_colls reduce_rec add_accu t colls = 
  try 
    apply_collisions_at_root_once reduce_rec Terms.try_no_var_id (fun t' -> add_accu t'; raise NoMatch) t colls
  with NoMatch -> ()

(* [simp_eq_diff add_accu t] applies a bunch of simplifications specific 
   to equalities to term [t].
   It calls the function [add_accu] on each obtained term. *)

let simp_eq_diff add_accu t = 
  match t.t_desc with
  | FunApp(f, [t1;t2]) when f.f_cat == Equal ->
      begin
      match (t1.t_desc, t2.t_desc) with
	(FunApp(f1,l1), FunApp(f2,l2)) when
	f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
	  add_accu (Terms.make_false())
      | (FunApp(f1,l1), FunApp(f2,l2)) when
	(f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	  add_accu (Terms.make_and_list (List.map2 Terms.make_equal l1 l2))
      | (Var(b1,l1), Var(b2,l2)) when
	(Terms.is_restr b1) &&
	(Proba.is_large_term t1  || Proba.is_large_term t2) && (b1 == b2) &&
	(Proba.add_elim_collisions b1 b1) ->
	  add_accu (Terms.make_and_list (List.map2 Terms.make_equal l1 l2))
      | (Var(b1,l1), Var(b2,l2)) when
	(Terms.is_restr b1) && (Terms.is_restr b2) &&
	(Proba.is_large_term t1 || Proba.is_large_term t2) &&
	(b1 != b2) && (Proba.add_elim_collisions b1 b2)->
	  add_accu (Terms.make_false())
      | (FunApp(f1,[]), FunApp(f2,[]) ) when
	f1 != f2 && (!Settings.diff_constants) ->
	  add_accu (Terms.make_false())
	          (* Different constants are different *)
      |	_ -> ()
      end
  | FunApp(f, [t1;t2]) when f.f_cat == Diff ->
      begin
      match (t1.t_desc, t2.t_desc) with
	(FunApp(f1,l1), FunApp(f2,l2)) when
	f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
	  add_accu (Terms.make_true())
      | (FunApp(f1,l1), FunApp(f2,l2)) when
	(f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	  add_accu (Terms.make_or_list (List.map2 Terms.make_diff l1 l2))
      | (Var(b1,l1), Var(b2,l2)) when
	(Terms.is_restr b1) &&
	(Proba.is_large_term t1  || Proba.is_large_term t2) && (b1 == b2) &&
	(Proba.add_elim_collisions b1 b1) ->
	  add_accu (Terms.make_or_list (List.map2 Terms.make_diff l1 l2))
      | (Var(b1,l1), Var(b2,l2)) when
	(Terms.is_restr b1) && (Terms.is_restr b2) &&
	(Proba.is_large_term t1 || Proba.is_large_term t2) &&
	(b1 != b2) && (Proba.add_elim_collisions b1 b2)->
	  add_accu (Terms.make_true())
      | (FunApp(f1,[]), FunApp(f2,[]) ) when
	f1 != f2 && (!Settings.diff_constants) ->
	  add_accu (Terms.make_true())
	          (* Different constants are different *)
      |	_ -> ()
      end
  | _ -> ()

(* [apply_eq_and_collisions_subterms_once reduce_rec equalities add_accu t] 
   applies the equalities coming from the equational theories, 
   the equality statements, the collisions given in the input 
   file, and the equalities given in [equalities] from left to right  
   to all subterms of [t]. It applies each equality once, and 
   calls the function [add_accu] on all terms generated by these equalities.
*)

let rec apply_eq_and_collisions_subterms_once reduce_rec equalities add_accu t = 
  let rec apply_list next_f seen = function
      [] -> ()
    | first::rest ->
	apply_eq_and_collisions_subterms_once reduce_rec equalities (fun t'' ->  
	  next_f (List.rev_append seen (t''::rest))
	    ) first;
        apply_list next_f (first::seen) rest
  in

  match t.t_desc with
    FunApp(f, [_;_]) when f.f_eq_theories != NoEq && f.f_eq_theories != Commut ->
      (* f is a binary function with an equational theory that is
	 not commutativity -> it is a product-like function *)
      (* We apply the statements only to subterms that are not products by f.
	 Subterms that are products by f are already handled above
	 using [match_term_root_or_prod_subterm]. *)
      apply_eq add_accu t equalities;
      apply_colls reduce_rec_impossible add_accu t f.f_statements;
      apply_colls reduce_rec add_accu t f.f_collisions;
      let l = Terms.simp_prod Terms.try_no_var_id (ref false) Terms.equal_terms f t in
      apply_list (fun l' -> add_accu (Terms.make_prod f l')) [] l
  | FunApp(f, ([t1;t2] as l)) when f.f_cat == Equal || f.f_cat == Diff ->
      apply_eq add_accu t equalities;
      simp_eq_diff add_accu t;
      apply_colls reduce_rec_impossible add_accu t f.f_statements;
      apply_colls reduce_rec add_accu t f.f_collisions;
      begin
	match Terms.get_prod_list Terms.try_no_var_id l with
	  ACUN(xor, neut) ->
	    let t' = Terms.app xor [t1;t2] in
	    apply_eq_and_collisions_subterms_once reduce_rec equalities (fun t'' ->
	      match t''.t_desc with
		FunApp(xor', [t1';t2']) when xor' == xor ->
		  add_accu (Terms.build_term2 t (FunApp(f, [t1';t2'])))
	      |	_ -> 
		  add_accu (Terms.build_term2 t (FunApp(f, [t'';Terms.app neut []])))
		    ) t'
	| CommutGroup(prod, inv, neut) ->
	    let rebuild_term t'' = 
	      (* calls add_accu on a term equal to FunApp(f, [t'', neut]) *)
	      let l = Terms.simp_prod Terms.try_no_var_id (ref false) Terms.equal_terms prod t'' in
	      let linv, lno_inv = List.partition (Terms.is_fun inv) l in
	      let linv_removed = List.map (function { t_desc = FunApp(f,[t]) } when f == inv -> t | _ -> assert false) linv in
	      add_accu (Terms.build_term2 t (FunApp(f, [ Terms.make_prod prod lno_inv; 
							 Terms.make_prod prod linv_removed ])))
	    in
	    apply_eq_and_collisions_subterms_once reduce_rec equalities rebuild_term (Terms.app prod [t1; Terms.app inv [t2]]);
	    (* Simplify the term t' = t2.t1^-1 just on the product level.
	       The simplification of smaller subterms has already been considered above. *)
	    let t' = Terms.app prod [t2; Terms.app inv [t1]] in
	    apply_eq rebuild_term t' equalities;
	    apply_colls reduce_rec_impossible rebuild_term t' prod.f_statements;
	    apply_colls reduce_rec rebuild_term t' prod.f_collisions
	| Group(prod, inv, neut) ->
	    let rebuild_term t'' =
		  (* calls add_accu on a term equal to FunApp(f, [t'', neut]) *)
		  let l = Terms.simp_prod Terms.try_no_var_id (ref false) Terms.equal_terms prod t'' in
		  let (inv_first, rest) = first_inv inv l in
		  let (inv_last_rev, rest_rev) = first_inv inv (List.rev rest) in
		(* if inv_first = [x1...xk], inv_last_rev = [y1...yl],
		   List.rev rest_rev = [z1...zm]
		   then the term we want to rewrite is
		   x1^-1...xk^-1.z1...zm.yl^-1...y1^-1 = neut
		   which is equal to
		   z1...zm = xk...x1.y1...yl *)
		  add_accu (Terms.build_term2 t (FunApp(f, [ Terms.make_prod prod (List.rev rest_rev) ; 
							     Terms.make_prod prod (List.rev_append inv_first inv_last_rev)])))
	    in
	    let l1 = Terms.simp_prod Terms.try_no_var_id (ref false) Terms.equal_terms prod (Terms.app prod [t1; Terms.app inv [t2]]) in
	    let l2 = Terms.remove_inverse_ends Terms.try_no_var_id (ref false) (prod, inv, neut) Terms.equal_terms l1 in
	    let rec apply_up_to_roll seen' rest' =
	      let t' = Terms.make_prod prod (rest' @ (List.rev seen')) in
	      (* Simplify the term t' = t2.t1^-1 just on the product level.
	         The simplification of smaller subterms is considered below. *)
	      apply_eq rebuild_term t' equalities;
	      apply_colls reduce_rec_impossible rebuild_term t' prod.f_statements;
	      apply_colls reduce_rec rebuild_term t' prod.f_collisions;
	      match rest' with
		[] -> ()
	      | a::rest'' -> apply_up_to_roll (a::seen') rest''
	    in
	    apply_up_to_roll [] l2;
	    let l3 = List.rev (List.map (Terms.compute_inv Terms.try_no_var_id (ref false) (prod, inv, neut)) l2) in
	    apply_up_to_roll [] l3;
	    (* Simplify smaller subterms *)
	    let l1 = Terms.simp_prod Terms.try_no_var_id (ref false) Terms.equal_terms prod t1 in
	    apply_list (fun l' -> add_accu (Terms.app f [Terms.make_prod prod l'; t2])) [] l1;
	    let l2 = Terms.simp_prod Terms.try_no_var_id (ref false) Terms.equal_terms prod t2 in
	    apply_list (fun l' -> add_accu (Terms.app f [t1; Terms.make_prod prod l'])) [] l2
	| _ -> 
	    apply_list (fun l' -> add_accu (Terms.build_term2 t (FunApp(f, l')))) [] l
      end
  | FunApp(f, l) ->
      apply_eq add_accu t equalities;
      apply_colls reduce_rec_impossible add_accu t f.f_statements;
      apply_colls reduce_rec add_accu t f.f_collisions;
      apply_list (fun l' -> add_accu (Terms.build_term2 t (FunApp(f, l')))) [] l
  | Var(b,l) -> 
      apply_eq add_accu t equalities;
      apply_list (fun l' -> add_accu (Terms.build_term2 t (Var(b, l')))) [] l
  | _ -> ()

(*
NOTE: we might want to reimplement apply_eq_reds to add all possible 
rewrites instead of just one.
*)

let apply_eq_and_collisions_subterms_once reduce_rec equalities add_accu t =
  let t' = Terms.apply_eq_reds Terms.try_no_var_id reduced t in
  if !reduced then add_accu t'; 
  apply_eq_and_collisions_subterms_once reduce_rec equalities add_accu t

(* In the function [apply_eq_and_collisions_subterms_once], we apply
   the equalities that come from the game (stored in [equalities]) in
   both directions, but we apply the statements and collisions given
   in the input file only in the direction specified in the input
   file.
   To be able to apply them at least a bit in both directions, 
   we reduce both the initial term [t] and the desired replacement [t']
   by [apply_eq_and_collisions_subterms_once]. The function [test_equal]
   reduces [t'] and calls [test_equal_rewrite_left], which reduces [t].
*)

(* [test_equal_rewrite_left depth reduce_rec equalities seen_left_terms left_terms right_terms]
   is true when a term in [left_terms] can be rewritten into a term in [right_terms] in
   at most [depth] steps. 
   [seen_left_terms] are terms already seen on the left, which do not need to be
   considered any more. *)

let rec test_equal_rewrite_left depth reduce_rec equalities seen_left_terms left_terms right_terms =
  if List.exists (fun tleft ->
    List.exists (Terms.equal_terms tleft) right_terms) left_terms then true else
  if depth <= 0 then false else
  let seen_terms = left_terms @ seen_left_terms in
  let new_terms = ref [] in
  List.iter (apply_eq_and_collisions_subterms_once reduce_rec equalities (fun t' ->
    if (not (List.exists (Terms.equal_terms t') seen_terms)) &&
       (not (List.exists (Terms.equal_terms t') (!new_terms))) then
      new_terms := t' :: (!new_terms)
			   )) left_terms;
  test_equal_rewrite_left (depth-1) reduce_rec equalities seen_terms (!new_terms) right_terms

(* [test_equal depth reduce_rec equalities t right_terms seen_right_terms] is true when
   [t] is equal to a term in [right_terms] by at most [depth] rewriting steps. 
   [seen_right_terms] are terms already seen on the right, which do not need to be
   considered any more. *)

let rec test_equal depth reduce_rec equalities t right_terms seen_right_terms =
  if List.exists (fun tright ->
    test_equal_rewrite_left depth reduce_rec equalities [] [t] right_terms) right_terms then true else
  if depth <= 0 then false else
  let seen_terms = right_terms @ seen_right_terms in
  let new_terms = ref [] in
  List.iter (apply_eq_and_collisions_subterms_once reduce_rec equalities (fun t' ->
    if (not (List.exists (Terms.equal_terms t') seen_terms)) &&
       (not (List.exists (Terms.equal_terms t') (!new_terms))) then
      new_terms := t' :: (!new_terms)
			   )) right_terms;
  test_equal (depth-1) reduce_rec equalities t (!new_terms) seen_terms


let check_equal g t t' and_facts and_proba =
  Proba.reset [] g;
  try 
    let facts' = get_facts_at t.t_facts in
      (*      print_string "Facts.check_equal: facts=";
              Display.display_list Display.display_term (facts'@and_facts);
              print_newline ();*)
    let simp_facts = Terms.auto_cleanup (fun () -> simplif_add_list no_dependency_anal ([],[],[]) (facts' @ and_facts)) in
    let r = (Terms.simp_equal_terms (try_no_var simp_facts) t t') || 
    (Terms.simp_equal_terms (try_no_var simp_facts) (simplify_term no_dependency_anal simp_facts t) (simplify_term no_dependency_anal simp_facts t')) ||
    (let equalities = ref [] in
    let (subst, facts, elsefind) = simp_facts in
    List.iter (fun t ->
      match t.t_desc with
	FunApp(f,[t1;t2]) when f.f_cat == Equal || f.f_cat == LetEqual ->
	  equalities := (t1,t2) :: (t2,t1) :: (!equalities)
      |	FunApp(f,[t1;t2]) when f.f_cat == Diff -> 
	  equalities := (t, Terms.make_true()) :: (Terms.make_equal t1 t2, Terms.make_false()) :: 
	                (Terms.make_true(), t) :: (Terms.make_false(), Terms.make_equal t1 t2) :: (!equalities)
      |	_ -> 
	  equalities := (t, Terms.make_true()) :: (Terms.make_true(), t) :: (!equalities)
	) (subst @ facts);
    test_equal (!Settings.max_replace_depth) (reduce_rec simp_facts) (!equalities) t [t'] []
    )
    in
    (* Add probability for eliminated collisions *)
    let proba = Proba.final_add_proba [] in
    (r, and_proba @ proba)
  with Contradiction ->
(*   print_string "Got contradiction";
    print_newline ();*)
    let proba = Proba.final_add_proba [] in
    (* May happen when the program point of t is in fact unreachable
       I say true anyway because the program point is unreachable. *)
    (true, and_proba @ proba)




(**** for debug: shows the derived facts at the given occurence ***)

let display_fact_info fact_info = 
  List.iter (fun f -> Display.display_term f; print_newline()) 
    (get_facts_at fact_info)

let rec display_facts_at p occ =
  if p.i_occ = occ then
    display_fact_info p.i_facts
  else
    match p.i_desc with
        Nil -> ()
      | Par (q,q') -> display_facts_at q occ;display_facts_at q' occ
      | Repl (_,q) -> display_facts_at q occ
      | Input (_,_,p) -> display_facts_at_op p occ

and display_facts_at_op p occ =
  if p.p_occ = occ then
    display_fact_info p.p_facts
  else
    match p.p_desc with
        Yield| EventAbort _ -> ()
      | Restr (_,p) -> display_facts_at_op p occ
      | Test (t,p,p') -> display_facts_at_t t occ;display_facts_at_op p occ;display_facts_at_op p' occ
      | Find (bl,p,_) -> List.iter (fun (_,_,t,p) -> display_facts_at_t t occ;display_facts_at_op p occ) bl; display_facts_at_op p occ
      | Output ((_,tl),t,q) -> List.iter (fun t -> display_facts_at_t t occ) tl;display_facts_at_t t occ;display_facts_at q occ
      | Let (pat,t,p,p') -> display_facts_at_pat pat occ;display_facts_at_t t occ;display_facts_at_op p occ;display_facts_at_op p' occ
      | EventP (t,p) -> display_facts_at_t t occ;display_facts_at_op p occ
      | Insert (_,_,_) | Get (_,_,_,_,_) -> Parsing_helper.internal_error "Get/Insert should not appear at this point"

and display_facts_at_t t occ =
  if t.t_occ = occ then
    display_fact_info t.t_facts
  else
    match t.t_desc with
        Var (_,tl) -> List.iter (fun t -> display_facts_at_t t occ) tl
      | ReplIndex _ -> ()
      | FunApp (_,tl) -> List.iter (fun t -> display_facts_at_t t occ) tl
      | TestE (t1,t2,t3) -> display_facts_at_t t1 occ;display_facts_at_t t2 occ;display_facts_at_t t3 occ
      | FindE (bl,t,_) -> List.iter (fun (_,_,t1,t2) -> display_facts_at_t t1 occ;display_facts_at_t t2 occ) bl; display_facts_at_t t occ
      | LetE (pat,t1,t2,topt) -> display_facts_at_pat pat occ;display_facts_at_t t1 occ;display_facts_at_t t2 occ;(match topt with Some t -> display_facts_at_t t occ| None -> ())
      | ResE (_,t) -> display_facts_at_t t occ
      | EventAbortE f -> ()

and display_facts_at_pat pat occ =
  match pat with
      PatVar _ -> ()
    | PatTuple (_,pl) -> List.iter (fun pat -> display_facts_at_pat pat occ) pl
    | PatEqual t -> display_facts_at_t t occ



