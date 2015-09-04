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
open Parsing_helper

let map_empty = Occ_map.empty

let simp_facts_id = ([],[],[])
let try_no_var_id t = t

(* Returns a list containing n times element x *)

let rec repeat n x =
  if n = 0 then [] else x :: (repeat (n-1) x)

(* Returns l without its n first elements *)

let rec skip n l = 
  try
    if n = 0 then l else skip (n-1) (List.tl l)
  with Failure "tl" ->
    failwith "Terms.skip"

(* Split l into two lists, first its n first elements, second
   the remaining of l *)

let rec split n l = 
  if n = 0 then ([],l) else
  match l with
    [] -> Parsing_helper.internal_error "split"
  | (a::l') -> let l1,l2 = split (n-1) l' in (a::l1,l2)


(* Find x in list l and return its position *)

let rec find_in_list x = function
    [] -> raise Not_found
  | (a::l) -> if x == a then 0 else 1 + find_in_list x l

(* Take a suffix of length n *)

let lsuffix n l =
  try
    skip (List.length l - n) l
  with Failure "Terms.skip" ->
    failwith "Terms.lsuffix"

(* Remove a suffix of length n *)

let remove_suffix n l =
  let (res, _) = split (List.length l - n) l in
  res

(* Compute intersections *)

let mem eqtest a l = List.exists (eqtest a) l

let intersect eqtest l1 l2 = List.filter (fun a2 -> mem eqtest a2 l1) l2

let rec intersect_list eqtest = function
    [] -> raise Contradiction
  | [a] -> a
  | (a::l) -> intersect eqtest a (intersect_list eqtest l)

(* union eqtest l1 l2 = l1 union l2 *)

let rec union eqtest l1 = function
    [] -> l1
  | (a::l) -> 
      if List.exists (eqtest a) l1 then
	union eqtest l1 l
      else
	a::(union eqtest l1 l)
	  
(* [map_union eqtest f l] = union of all [f a] for [a] in [l] *)

let rec map_union eqtest f = function
    [] -> []
  | (a::l) -> union eqtest (f a) (map_union eqtest f l)

(* Equality tests *)

let equal_lists eq l1 l2 =
  (List.length l1 == List.length l2) && 
  (List.for_all2 eq l1 l2)

let equal_mset mset1 mset2 =
  match (mset1, mset2) with
    (MOneBinder b1, MOneBinder b2) -> b1 == b2
  | x, y -> x == y

let equal_rset rset1 rset2 =
  match (rset1, rset2) with
    (All, All) | (Minimal, Minimal) -> true
  | (OneBinder b1, OneBinder b2) -> b1 == b2
  | _ -> false

let equal_merge_mode m1 m2 =
  match (m1,m2) with
    (MNoBranchVar, MNoBranchVar) | (MCreateBranchVar, MCreateBranchVar) -> true
  | (MCreateBranchVarAtProc (pl1, cur_array1), MCreateBranchVarAtProc (pl2, cur_array2)) ->
      (equal_lists (==) pl1 pl2) && (equal_lists (==) cur_array1 cur_array2)
  | (MCreateBranchVarAtTerm (tl1, cur_array1), MCreateBranchVarAtTerm (tl2, cur_array2)) ->
      (equal_lists (==) tl1 tl2) && (equal_lists (==) cur_array1 cur_array2)
  | _ -> false

let equal_query q1 q2 =
  match (q1,q2) with
    (QSecret b1, QSecret b2) -> b1 == b2
  | (QSecret1 b1, QSecret1 b2) -> b1 == b2
  | _ -> false

let equal_instruct i1 i2 =
  match i1,i2 with
    (ExpandIfFindGetInsert, ExpandIfFindGetInsert) -> true
  | (Simplify l1, Simplify l2) -> equal_lists (=) l1 l2
  | (GlobalDepAnal (b1,l1), GlobalDepAnal (b2,l2)) -> (b1 == b2) && (equal_lists (=) l1 l2)
  | (RemoveAssign rset1, RemoveAssign rset2) -> equal_rset rset1 rset2
  | (SArenaming b1, SArenaming b2) -> b1 == b2
  | (MoveNewLet mset1, MoveNewLet mset2) -> equal_mset mset1 mset2
  | (CryptoTransf (eq1, bl1), CryptoTransf (eq2, bl2)) -> 
      (eq1 == eq2) && (equal_lists (==) bl1 bl2)
  | (InsertEvent(s1,n1), InsertEvent(s2,n2)) ->
      (s1 = s2) && (n1 == n2)
  | (InsertInstruct(s1,_,n1,_), InsertInstruct(s2,_,n2,_)) ->
      (s1 = s2) && (n1 == n2)
  | (ReplaceTerm(s1,_,n1,_), ReplaceTerm(s2,_,n2,_)) ->
      (s1 = s2) && (n1 == n2)
  | (MergeArrays(bl1,m1), MergeArrays(bl2,m2)) ->
      (equal_lists (equal_lists (fun (b1,ext1) (b2, ext2) -> (b1 == b2) && (ext1 = ext2))) bl1 bl2) &&
      (equal_merge_mode m1 m2)
  | (MergeBranches, MergeBranches) -> true
  | (Proof ql1, Proof ql2) ->
      equal_lists (fun ((q1,n1),p1) ((q2,n2),p2) -> (equal_query q1 q2) && (n1 = n2) && (p1 = p2)) ql1 ql2
  | _ -> false

let add_eq a l =
  if List.exists (equal_instruct a) l then l else a::l

(* Create an interval type from a parameter *)

let type_for_param_table = Hashtbl.create 7

let type_for_param p =
  try 
    Hashtbl.find type_for_param_table p 
  with Not_found ->
    let t = { tname = "[1," ^ p.pname ^"]";
	      tcat = Interv p;
	      toptions = Settings.tyopt_BOUNDED;
	      tsize = 0;
              timplsize = None;
              tpredicate = None;
              timplname = None;
              tserial = None;
              trandom = None }
    in
    Hashtbl.add type_for_param_table p t;
    t

(* Get a parameter from an interval type *)

let param_from_type t =
  match t.tcat with
    Interv p -> p
  | _ -> internal_error "Interval type expected"

(* New occurrence *)

let occ = ref 0
let max_occ = ref 100

let new_occ() =
  incr occ;
  if !occ > !max_occ then max_occ := !occ;
  !occ

(* Binder from term *)

let binder_from_term t =
  match t.t_desc with
    Var(b,_) -> b
  | _ -> internal_error "Binder term expected"

let binderref_from_term t =
  match t.t_desc with
    Var(b,l) -> (b,l)
  | _ -> internal_error "Binder term expected"

let repl_index_from_term t =
  match t.t_desc with
    ReplIndex(b) -> b
  | _ -> internal_error "Replication index term expected"

let build_term t desc =
  { t_desc = desc;
    t_type = t.t_type;
    t_occ = new_occ(); 
    t_max_occ = 0;
    t_loc = Parsing_helper.dummy_ext;
    t_incompatible = map_empty;
    t_facts = None }

(* build_term2 is the same as build_term, except that it keeps the
   occurrence of t. This is useful in particular so that occurrences
   are kept in term manipulations by simplification, to be able to
   designate a term by occurrence *)

let build_term2 t desc =
  { t_desc = desc;
    t_type = t.t_type;
    t_occ = t.t_occ;
    t_max_occ = 0;
    t_loc = t.t_loc;
    t_incompatible = map_empty;
    t_facts = None }

let build_term3 t desc =
  { t_desc = desc;
    t_type = t.t_type;
    t_occ = new_occ();
    t_max_occ = 0;
    t_loc = t.t_loc;
    t_incompatible = map_empty;
    t_facts = None }

let build_term_type ty desc =
  { t_desc = desc;
    t_type = ty;
    t_occ = new_occ();
    t_max_occ = 0;
    t_loc = Parsing_helper.dummy_ext;
    t_incompatible = map_empty;
    t_facts = None }

let new_term ty ext desc =
  { t_desc = desc;
    t_type = ty;
    t_occ = new_occ();
    t_max_occ = 0;
    t_loc = ext;
    t_incompatible = map_empty;
    t_facts = None }  
    
let term_from_repl_index b =
  build_term_type b.ri_type (ReplIndex b)

let term_from_binder b =
  build_term_type b.btype (Var(b, List.map term_from_repl_index b.args_at_creation))

let term_from_binderref (b,l) =
  build_term_type b.btype (Var(b, l))

let binderref_from_binder b =
  (b, List.map term_from_repl_index b.args_at_creation)

let is_args_at_creation b l =
  List.for_all2 (fun ri t -> 
    match t.t_desc with
      ReplIndex ri' -> ri == ri'
    | _ -> false) b.args_at_creation l

let app f l =
  build_term_type (snd f.f_type) (FunApp(f,l)) 

(* Process from desc *)

let iproc_from_desc d = { i_desc = d; i_occ = new_occ(); i_max_occ = 0; 
			  i_incompatible = map_empty; i_facts = None }

let oproc_from_desc d = { p_desc = d; p_occ = new_occ(); p_max_occ = 0;
			  p_incompatible = map_empty; p_facts = None }

let iproc_from_desc2 p d = { i_desc = d; i_occ = p.i_occ; i_max_occ = 0; 
			     i_incompatible = p.i_incompatible; 
			     i_facts = p.i_facts }

let oproc_from_desc2 p d = { p_desc = d; p_occ = p.p_occ; p_max_occ = 0;
			     p_incompatible = p.p_incompatible; 
			     p_facts = p.p_facts }

let iproc_from_desc3 p d = { i_desc = d; i_occ = p.i_occ; i_max_occ = 0; 
			     i_incompatible = map_empty; i_facts = None }

let oproc_from_desc3 p d = { p_desc = d; p_occ = p.p_occ; p_max_occ = 0;
			     p_incompatible = map_empty; p_facts = None }

(* Constant for each type *)

module HashedType =
  struct
    type t = Types.typet
    let equal = (==)
    (* The hash function must use only parts that are not modified,
       otherwise, we may have the same element with several different hashes *)
    let hash t = Hashtbl.hash t.tname
  end

module TypeHashtbl = Hashtbl.Make(HashedType)

let cst_for_type_table = TypeHashtbl.create 7

let cst_for_type ty =
  let f = 
    try
      TypeHashtbl.find cst_for_type_table ty
    with Not_found ->
      let r = { f_name = "cst_" ^ ty.tname;
		f_type = [],ty;
		f_cat = Std;
		f_options = 0;
		f_statements = [];
		f_collisions = [];
		f_eq_theories = NoEq;
                f_impl = No_impl;
                f_impl_inv = None }
      in
      TypeHashtbl.add cst_for_type_table ty r;
      r
  in
  build_term_type ty (FunApp(f,[]))

(* Is a variable defined by a restriction ? *)

let is_restr b =
  List.for_all (function 
      { definition = DProcess { p_desc = Restr _} } -> true
    | { definition = DTerm ({ t_desc = ResE _}) } -> true
    | { definition = DFunRestr } -> true
    | _ -> false) b.def

(* Is a variable defined by an assignment ? *)

let is_assign b =
  List.for_all (function 
      { definition = DProcess { p_desc = Let _} } -> true
    | { definition = DTerm { t_desc = LetE _ }} -> true
    | _ -> false) b.def

(* Links *)

let current_bound_vars = ref []

let link v l =
  current_bound_vars := v :: (!current_bound_vars);
  v.link <- l

let cleanup () =
  List.iter (fun v -> v.link <- NoLink) (!current_bound_vars);
  current_bound_vars := []

let auto_cleanup f =
  let tmp_bound_vars = !current_bound_vars in
  current_bound_vars := [];
  try
    let r = f () in
    List.iter (fun v -> v.link <- NoLink) (!current_bound_vars);
    current_bound_vars := tmp_bound_vars;
    r
  with x ->
    List.iter (fun v -> v.link <- NoLink) (!current_bound_vars);
    current_bound_vars := tmp_bound_vars;
    raise x

(* Equality *)

(* [compute_inv try_no_var reduced (f, inv, n) t] returns a term equal to 
   [inv(t)]. 
   [(f, inv,n)] is supposed to be a group, with product [f],
   inverse function [inv], and neutral element [n]. 
   [reduced] is set to true when a simplification occurred
   during the computation. 
   [try_no_var] is explained in the function [simp_main_fun]. *)

let rec compute_inv try_no_var reduced (f, inv, n) t =
  let t_no_var = try_no_var t in
  match t_no_var.t_desc with
    FunApp(inv', [t']) when inv' == inv -> 
      (* inv(inv(x)) = x *)
      reduced := true;
      t'
  | FunApp(f', [t1;t2]) when f' == f ->
      (* inv(x.y) = inv(y).inv(x) *)
      reduced := true;
      build_term t (FunApp(f, [compute_inv try_no_var reduced (f,inv,n) t2; compute_inv try_no_var reduced (f,inv,n) t1]))
  | FunApp(n', []) when n' == n ->
      (* inv(n) = n *)
      reduced := true;
      t_no_var
  | _ ->
      build_term t (FunApp(inv, [t]))

(* Simplification function:
   [simp_main_fun try_no_var reduced f t] simplifies term [t].
   [f] is a binary function with an equational theory. 
   [simp_main_fun] returns a list of terms [l], such that [t] is equal to
   the product of the elements of [l] by function [f].
   [reduced] is set to true when [t] has really been simplified.
   [try_no_var] is a function from terms to terms that tries to replace
   variables with their values. It leaves non-variable terms unchanged.
   It can be the identity when we do not have information on the values
   of variables.
   ([simp_main_fun] does not consider cancellations between terms in
   ACUN or group equational theories, which are considered below by
   function [simp_prod].) *)

let rec simp_main_fun try_no_var reduced f t =
  match f.f_eq_theories, (try_no_var t).t_desc with
    (Assoc | AssocN _ | AssocCommut | AssocCommutN _ | ACUN _ | 
     Group _ | CommutGroup _), FunApp(f', [t1;t2]) when f == f' -> 
      (simp_main_fun try_no_var reduced f t1) @ 
      (simp_main_fun try_no_var reduced f t2)
  | (Group(f'',inv,n) | CommutGroup(f'',inv,n)), FunApp(inv', [t1]) when inv' == inv ->
      let reduced' = ref false in
      let t' = compute_inv try_no_var reduced' (f'',inv,n) t1 in
      if !reduced' then
	begin
	  reduced := true;
	  simp_main_fun try_no_var reduced f t'
	end
      else
	[t]
  | (AssocN(_,n) | AssocCommutN(_,n) | ACUN(_,n) | Group(_,_,n) | 
     CommutGroup(_,_,n)), FunApp(n', []) when n == n' ->
      (* Eliminate the neutral element *)
      reduced := true;
      []
  | _ -> [t]

(* [remove_elem sub_eq a l] returns list [l] with one
   occurrence of element [a] removed. Function [sub_eq]
   is used to test equality between elements.
   When [l] does not contain [a], raises [Not_found]. *)

let rec remove_elem sub_eq a = function
    [] -> raise Not_found 
  | (a'::l) ->
      if sub_eq a a' then l else a'::(remove_elem sub_eq a l)

(* [remove_duplicates reduced sub_eq l] returns list [l]
   after removing duplicate elements. Function [sub_eq]
   is used to test equality between elements.
   [reduced] is set to true when some elements have been removed. *)

let rec remove_duplicates reduced sub_eq = function
    [] -> []
  | (a::l) ->
      try 
	let l' = remove_elem sub_eq a l in
	reduced := true;
	remove_duplicates reduced sub_eq l'
      with Not_found ->
	a::(remove_duplicates reduced sub_eq l)

(* [equal_up_to_order sub_eq l1 l2] returns true when the
   lists [l1] and [l2] are equal up to the ordering of their
   elements. 
   The function [sub_eq] is used to test equality between elements. *)

let rec equal_up_to_order sub_eq l1 l2 =
  match l1,l2 with
    [],[] -> true
  | [],_ | _,[] -> false
  | (a::l,_) ->
      try
	let l2' = remove_elem sub_eq a l2 in
	equal_up_to_order sub_eq l l2'
      with Not_found ->
	false

(* [equal_up_to_roll sub_eq l1 l2] returns true when [l1]
   contains the same elements as [l2], in the same order,
   but the lists may be rotated, that is,
   l1 = [t1;...;tn] and l2 = [tk;...;tn;t1;...;t_{k-1}].
   Function [sub_eq] is used to test equality between elements. *)

let rec equal_up_to_roll_rec sub_eq l1 seen2 rest2 =
  (List.for_all2 sub_eq l1 (rest2 @ (List.rev seen2))) ||
  (match rest2 with
    [] -> false
  | (a::rest2') ->
      equal_up_to_roll_rec sub_eq l1 (a::seen2) rest2'
	)

let equal_up_to_roll sub_eq l1 l2 =
  (List.length l1 == List.length l2) && 
  (equal_up_to_roll_rec sub_eq l1 [] l2)

(* [get_neutral f] returns the neutral element of the equational
   theory of the function symbol [f]. *)

let get_neutral f =
  match f.f_eq_theories with
    ACUN(_,n) | Group(_,_,n) | CommutGroup(_,_,n) -> n
  | _ -> Parsing_helper.internal_error "equational theory has no neutral element in Terms.get_neutral"

(* [get_prod try_no_var t] returns the equational theory of the root
   function symbol of term [t], when it is a product
   in a group or xor. *)

let get_prod try_no_var t =
  match (try_no_var t).t_desc with
    FunApp(f,[_;_]) ->
      begin
	match f.f_eq_theories with
	  Group(prod,_,_) | CommutGroup(prod,_,_) 
	| ACUN(prod,_) when prod == f -> 
	    f.f_eq_theories
	| _ -> NoEq
      end
  | _ -> NoEq

(* [get_prod_list try_no_var l] returns the equational theory of the root
   function symbol of a term in [l], when it is a product
   in a group or xor. *)

let rec get_prod_list try_no_var = function
    [] -> NoEq
  | t::l ->
      match (try_no_var t).t_desc with
	FunApp(f,[_;_]) ->
	  begin
	  match f.f_eq_theories with
	    Group(prod,_,_) | CommutGroup(prod,_,_) 
	  | ACUN(prod,_) when prod == f -> 
	      f.f_eq_theories
	  | _ -> get_prod_list try_no_var l
	  end
      |	_ -> get_prod_list try_no_var l

(* [remove_inverse_ends simp_facts reduced group_th l] removes the
   inverse elements at the two ends of the list [l]. In a non-commutative group,
   the product of the elements [l] is the neutral element if and only if the
   product of the resulting list is: x * t * x^-1 = e iff t = e by multiplying
   on the left by x^-1 and on the right by x. 
   [simp_facts] collects the rewrite rules corresponding to known equalities
   and other known facts, which we use in order to replace variables with their values and
   to test equality between terms.
   [group_th = (f, inv,n)] is supposed to be a group, with product [f],
   inverse function [inv], and neutral element [n].    
   [reduced] is set to true when some elements have been removed. *)

let rec cut_list n accu l = 
  if n = 0 then (accu, l) else
  match l with
    [] -> (accu, [])
  | a::l' -> cut_list (n-1) (a::accu) l'

let rec remove_inverse_prefix simp_facts reduced group_th l1 l2 =
  match l1, l2 with
    t1::r1, t2::r2 when simp_equal_terms simp_facts true t1 (compute_inv (try_no_var simp_facts) (ref false) group_th t2) -> 
      reduced := true;
      remove_inverse_prefix simp_facts reduced group_th r1 r2
  | _ -> (l1,l2)    

and remove_inverse_ends simp_facts reduced group_th l = 
  let n = (List.length l) / 2 in
  let half1, half2 = cut_list n [] l in
  let half1', half2' = remove_inverse_prefix simp_facts reduced group_th half1 half2 in
  List.rev_append half1' half2'

(* [remove_inverse simp_facts reduced group_th l] returns list [l]
   after removing elements that are inverse of one another. 
   [simp_facts], [reduced], and [group_th] are as above. *)

and remove_inverse simp_facts reduced group_th = function
    [] -> []
  | (a::l) ->
      try 
	let a_inv = compute_inv (try_no_var simp_facts) (ref false) group_th a in
	let l' = remove_elem (simp_equal_terms simp_facts true) a_inv l in
	reduced := true;
	remove_inverse simp_facts reduced group_th l'
      with Not_found ->
	a::(remove_inverse simp_facts reduced group_th l)

(* [remove_consecutive_inverse simp_facts reduced group_th seen_l l]
   removes consecutive elements of [l] that are inverses of one another.
   [seen_l] corresponds to the part of [l] already examined by the algorithm,
   in reverse order. The algorithm always tries to eliminate the first
   element of [seen_l] and the first element of [l].
   [simp_facts], [reduced], and [group_th] are as above. *)

and remove_consecutive_inverse simp_facts reduced group_th seen_l l = 
  match (seen_l, l) with
    [],[] -> []
  | [],a::l' -> remove_consecutive_inverse simp_facts reduced group_th [a] l'
  | _ ,[] -> List.rev seen_l
  | a::seen_l', a'::l' ->
      let a_inv = compute_inv (try_no_var simp_facts) (ref false) group_th a in
      if simp_equal_terms simp_facts true a_inv a' then
	begin
	  reduced := true;
	  remove_consecutive_inverse simp_facts reduced group_th seen_l' l'
	end
      else
	remove_consecutive_inverse simp_facts reduced group_th (a'::seen_l) l'


(* Simplification function:
   [simp_prod simp_facts reduced f t] simplifies term [t].
   [f] is a binary function with an equational theory. 
   [simp_prod] returns a list of terms [l], such that [t] is equal to
   the product of the elements of [l] by function [f].
   [simp_facts] collects the rewrite rules corresponding to known equalities
   and other known facts, which we use in order to replace variables with their values and
   to test equality between terms.
   [reduced] is set to true when [t] has really been simplified. *)

and simp_prod simp_facts reduced f t =
  let l = simp_main_fun (try_no_var simp_facts) reduced f t in
  match f.f_eq_theories with
    ACUN _ -> 
      (* Remove duplicates from the list, since they cancel out *)
      remove_duplicates reduced (simp_equal_terms simp_facts true) l
  | Group(f',inv,n) ->
      (* Remove pairs formed of an element immediately followed by its inverse,
	 since they cancel out. *)
      remove_consecutive_inverse simp_facts reduced (f',inv,n) [] l
  | CommutGroup(f',inv,n) ->
      (* Remove pairs of an element and its inverse since they cancel out *)
      remove_inverse simp_facts reduced (f',inv,n) l
  | _ -> l


(* [try_no_var simp_facts t] returns [t] unchanged when it
   is a function application and tries to replace it with its value
   using the rewrite rules in [simp_facts] when it is a variable.
   See facts.ml for additional information on [simp_facts].

   The functions [apply_subst_list] and [normalize_var] are helper functions
   to define [try_no_var].

   [apply_subst_list t subst] applies a rewrite rule in [subst]
   to the term [t] (only at the root of [t]) and returns the reduced
   term, if possible. Otherwise, it just returns [t] itself. *)

and apply_subst_list t = function
    [] -> t
  | tsubst::rest -> 
     match tsubst.t_desc with
       FunApp(f,[redl;redr]) when f.f_cat == Equal || f.f_cat == LetEqual ->
         begin
           if equal_terms t redl then 
	     redr
           else
	     apply_subst_list t rest
         end
     | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"

(* [normalize_var subst t] normalizes the term [t] (which must contain
   only variables and replication indices) using the rewrite rules
   in [subst].
   Since the RHS of rewrite rules is already normalized,
   it is enough to apply rewrite rules once at each variable 
   symbol from the inside to the outside to normalize the term. *)

and normalize_var subst2 t =
  match t.t_desc with
    Var(b,l) ->
      let l' = List.map (normalize_var subst2) l in
      let t' = build_term2 t (Var(b,l')) in
      apply_subst_list t' subst2
  | ReplIndex _ -> 
      apply_subst_list t subst2
  | FunApp _ ->
      (* This property requires variables not to contain functions.
	 This is true now, but may change in the future. *)
      Parsing_helper.internal_error "FunApp should not occur in normalize_var"
  | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ -> 
      Parsing_helper.internal_error "If, find, let, and new should not occur in normalize_var"

and try_no_var (subst2, _, _) t =
  if subst2 == [] then t else
  match t.t_desc with
    Var _ | ReplIndex _ -> 
      normalize_var subst2 t 
  | _ -> t

(* Equality test *)

(* [simp_equal_terms simp_facts normalize_root t1 t2] returns true when
   the terms [t1] and [t2] are equal. It uses the rewrite rules in
   [simp_facts] to reduce the terms in order to infer more equalities.
   When [normalize_root] is false, the rewrite rules in [simp_facts]
   are not applied at the root of the terms [t1] and [t2]. *)

and simp_equal_terms simp_facts normalize_root t1 t2 = 
  if (simp_facts == simp_facts_id) || (not normalize_root) then
    simp_equal_terms1 simp_facts t1 t2
  else
    (simp_equal_terms1 simp_facts_id t1 t2) ||
    (let t1' = normalize simp_facts t1 in
    let t2' = normalize simp_facts t2 in
    simp_equal_terms1 simp_facts t1' t2')

and simp_equal_terms1 simp_facts t1 t2 =
  match (t1.t_desc, t2.t_desc) with
    Var(b1,l1),Var(b2,l2) ->
      (b1 == b2) && (List.for_all2 equal_terms l1 l2)
  | ReplIndex b1, ReplIndex b2 -> b1 == b2
  | FunApp(f1, [t1;t1']), FunApp(f2, [t2;t2']) when 
      f1 == f2 && (f1.f_cat == Equal || f1.f_cat == Diff) ->
	(* It is important to test this case before the commutative
	   function symbols: = and <> are also commutative function
	   symbols. *)
	begin
	  (* In a group, when t1/t1' = t2/t2', we have t1 = t1' if and only if t2 = t2'.
	     With xor, when t1 xor t1' = t2 xor t2', we have t1 = t1' if and only if t2 = t2'. *)
	  match get_prod_list (try_no_var simp_facts) [t1;t1';t2;t2'] with
	    ACUN(xor,_) ->
	      simp_equal_terms simp_facts true (app xor [t1;t1']) (app xor [t2;t2'])
	  | CommutGroup(prod,inv,_) ->
	      (simp_equal_terms simp_facts true (app prod [t1; app inv [t1']])
		(app prod [t2; app inv [t2']])) ||
	      (simp_equal_terms simp_facts true (app prod [t1; app inv [t1']]) 
		(app prod [t2'; app inv [t2]]))
	  | Group(prod,inv,neut) ->
	      (* For non-commutative groups, I can still commute a term
		 and its inverse, so I try all possibilities. 
		 t1 = t1' iff t1/t1' = neut iff the product of the elements of [l1] is neut 
		          iff the product of the elements of [l1'] is neut 
		 Similarly, t2 = t2' iff the product of the elements of [l2'] is neut.
		 The product of the elements of [l2''] is the inverse of 
		 the product of the elements of [l2'],
		 so one is neut iff the other is.
		 *)
	      let l1 = simp_prod simp_facts (ref false) prod (app prod [t1; app inv [t1']]) in
	      let l1' = remove_inverse_ends simp_facts (ref false) (prod, inv, neut) l1 in
	      let l2 = simp_prod simp_facts (ref false) prod (app prod [t2; app inv [t2']]) in
	      let l2' = remove_inverse_ends simp_facts (ref false) (prod, inv, neut) l2 in
	      (equal_up_to_roll (simp_equal_terms simp_facts true) l1' l2') || 
	      (let l2'' = List.rev (List.map (compute_inv (try_no_var simp_facts) (ref false) (prod, inv, neut)) l2') in
	      equal_up_to_roll (simp_equal_terms simp_facts true) l1' l2'')
	  | _ -> 
	      ((simp_equal_terms simp_facts true t1 t2) && (simp_equal_terms simp_facts true t1' t2')) ||
	      ((simp_equal_terms simp_facts true t1 t2') && (simp_equal_terms simp_facts true t1' t2))
	end
  | FunApp(f1,[t1;t1']),FunApp(f2,[t2;t2']) when f1 == f2 && f1.f_eq_theories = Commut ->
      (* Commutative function symbols *)
      ((simp_equal_terms simp_facts true t1 t2) && (simp_equal_terms simp_facts true t1' t2')) ||
      ((simp_equal_terms simp_facts true t1 t2') && (simp_equal_terms simp_facts true t1' t2))
  | FunApp({f_eq_theories = (Group(f,inv',n) | CommutGroup(f,inv',n)) } as inv, [t1']), _ when inv' == inv ->
      (* inv is an inverse function *)
      let reduced = ref false in
      let t1_simp = compute_inv (try_no_var simp_facts) reduced (f,inv',n) t1' in
      if !reduced then simp_equal_terms simp_facts true t1_simp t2 else 
      begin
        match t2.t_desc with
          FunApp({f_eq_theories = (Group(f2,inv2',n2) | CommutGroup(f2,inv2',n2)) } as inv2, [t2']) when inv2' == inv2 ->
            (* inv2 is an inverse function *)
            let reduced = ref false in
            let t2_simp = compute_inv (try_no_var simp_facts) reduced (f2,inv2',n2) t2' in
            if !reduced then simp_equal_terms simp_facts true t1 t2_simp else 
            (inv == inv2) && (simp_equal_terms simp_facts true t1' t2')
        | FunApp(f2, [_;_]) when f2.f_eq_theories != NoEq && f2.f_eq_theories != Commut ->
            (* f2 is a binary function with an equational theory that is
	       not commutativity nor inverse -> it is a product-like function *)
            let l2 = simp_prod simp_facts (ref false) f2 t2 in
            begin
	      match l2 with
	        [] -> simp_equal_terms simp_facts true t1 (build_term t2 (FunApp(get_neutral f2, [])))
	      | [t] -> simp_equal_terms simp_facts true t1 t
	      | _ -> (* t2 is a product and t1 is not (it is an inverse), so they cannot be equal *)
	         false
            end
        | _ -> (* t2 is not an inverse nor a product, it cannot be equal to t1 *) false
      end
  | FunApp(f1,[_;_]),_ when f1.f_eq_theories != NoEq && f1.f_eq_theories != Commut ->
      (* f1 is a binary function with an equational theory that is
	 not commutativity nor inverse -> it is a product-like function *)
      let l1 = simp_prod simp_facts (ref false) f1 t1 in
      begin
	match l1 with
	  [] -> simp_equal_terms simp_facts true (build_term t1 (FunApp(get_neutral f1, []))) t2
	| [t] -> simp_equal_terms simp_facts true t t2
	| _ -> 
	    let l2 = simp_prod simp_facts (ref false) f1 t2 in
	    match f1.f_eq_theories with
	      NoEq | Commut -> Parsing_helper.internal_error "equal_terms: cases NoEq, Commut should have been eliminated"
	    | AssocCommut | AssocCommutN _ | CommutGroup _ | ACUN _ ->
		(* Commutative equational theories: test equality up to ordering *)
		(List.length l1 == List.length l2) &&
		(equal_up_to_order (simp_equal_terms simp_facts true) l1 l2)
	    | Assoc | AssocN _ | Group _ -> 
		(* Non-commutative equational theories: test equality in the same order *)
		equal_lists (simp_equal_terms simp_facts true) l1 l2		
      end
  | _, FunApp({f_eq_theories = (Group(f,inv',n) | CommutGroup(f,inv',n)) } as inv, [t2']) when inv == inv' ->
      (* inv is an inverse function *)
      let reduced = ref false in
      let t2_simp = compute_inv (try_no_var simp_facts) reduced (f,inv',n) t2' in
      if !reduced then simp_equal_terms simp_facts true t1 t2_simp else 
      (* t1 is not a product nor an inverse, otherwise the previous cases 
         would have been triggered, so t1 cannot be equal to t2 *)
      false
  | _, FunApp(f2, [_;_]) when f2.f_eq_theories != NoEq && f2.f_eq_theories != Commut ->
      (* f2 is a binary function with an equational theory that is
	 not commutativity nor inverse -> it is a product-like function *)
      let l2 = simp_prod simp_facts (ref false) f2 t2 in
      begin
	match l2 with
	  [] -> simp_equal_terms simp_facts true t1 (build_term t2 (FunApp(get_neutral f2, [])))
	| [t] -> simp_equal_terms simp_facts true t1 t
	| _ -> (* t2 is a product and t1 is not (otherwise the previous case
		  would have been triggered), so they cannot be equal *)
	    false
      end
  | FunApp(f1,l1),FunApp(f2,l2) ->
      (f1 == f2) && (List.for_all2 (simp_equal_terms simp_facts true) l1 l2)
  | TestE(t1,t2,t3), TestE(t1',t2',t3') ->
      (simp_equal_terms simp_facts true t1 t1') && (simp_equal_terms simp_facts true t2 t2') && (simp_equal_terms simp_facts true t3 t3')
  | FindE(l,t3,find_info),FindE(l',t3',find_info') ->
      (* Could do modulo renaming of bl and bl'! *)
      (equal_lists (fun (bl,def_list,t1,t2) (bl',def_list',t1',t2') ->
	(equal_lists (fun (b1,b2) (b1', b2') -> (b1 == b1') && (b2 == b2')) bl bl') && 
	(equal_def_lists def_list def_list') && 
	(simp_equal_terms simp_facts true t1 t1') && (simp_equal_terms simp_facts true t2 t2')) l l') && 
      (simp_equal_terms simp_facts true t3 t3') &&
      (find_info == find_info')
  | LetE(pat, t1, t2, topt), LetE(pat', t1', t2', topt') ->
      (equal_pats simp_facts pat pat') &&
      (simp_equal_terms simp_facts true t1 t1') &&
      (simp_equal_terms simp_facts true t2 t2') &&
      (match topt, topt' with
	None, None -> true
      |	Some t3, Some t3' -> simp_equal_terms simp_facts true t3 t3'
      |	_ -> false)
  | ResE(b,t), ResE(b',t') ->
      (b == b') && (simp_equal_terms simp_facts true t t')
  | EventAbortE(f), EventAbortE(f') -> 
      f == f'
  | _ -> false

and equal_terms t1 t2 = simp_equal_terms1 simp_facts_id t1 t2

and equal_def_lists def_list def_list' =
  equal_lists equal_binderref def_list def_list'

and equal_binderref (b,l) (b',l') =
  (b == b') && (List.for_all2 equal_terms l l')

and equal_pats simp_facts p1 p2 =
  match p1,p2 with
    PatVar b, PatVar b' -> b == b'
  | PatTuple (f,l), PatTuple (f',l') -> (f == f') && (List.for_all2 (equal_pats simp_facts) l l')
  | PatEqual t, PatEqual t' -> simp_equal_terms simp_facts true t t'
  | _ -> false



(* [apply_subst_list_fun simp_facts t subst] applies a 
   rewrite rule [subst] to the term [t] (only at the root)
   and returns the reduced term, if possible. Otherwise,
   it just returns [t] itself.
   It uses the equalities in [simp_facts] to help establishing
   that [t] is equal to the left-hand side of a rewrite rule.
   The equalities in [simp_facts] are applied only to strict 
   subterms of [t] and of the LHS of a rewrite rule, because
   applying them at the root of [t]  would mean applying another 
   rewrite rule, and applying them at the root of the LHS of a
   rewrite rule is impossible since the root of rewrite rules
   is already normalized.
 *)

and apply_subst_list_fun simp_facts t = function
    [] -> t
  | tsubst::rest -> 
     match tsubst.t_desc with
       FunApp(f,[redl;redr]) when f.f_cat == Equal || f.f_cat == LetEqual ->
         begin
           if simp_equal_terms simp_facts false t redl then 
	     redr
           else
	     apply_subst_list_fun simp_facts t rest
         end
     | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"

(* [normalize simp_facts t] normalizes the term [t]
   using the rewrite rules in [simp_facts]. 
   The root of [t] is guaranteed to be normalized.
   Rewrite rules of [simp_facts] may still be applicable
   to strict subterms of the result. 
   When [t] is a variable, we use [normalize_var].
   When it is a function symbol, we apply a rewrite rule of
   [simp_facts] once at the root (possibly applying rewrite rules
   of [simp_facts] to strict subterms to allow this rewriting),
   if possible. This is enough because the RHS of rewrite rules is 
   already normalized at the root. *)
	   
and normalize ((subst2, _, _) as simp_facts) t =
  match t.t_desc with
    FunApp(f,l) ->
      apply_subst_list_fun simp_facts t subst2
  | Var _ | ReplIndex _ -> 
      normalize_var subst2 t 
  | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ -> 
      t

let equal_term_lists l1 l2 =
  equal_lists equal_terms l1 l2

let equal_action a1 a2 =
  match a1, a2 with
    AFunApp f, AFunApp f' -> f == f'
  | APatFunApp f, APatFunApp f' -> f == f'
  | AReplIndex, AReplIndex -> true
  | AArrayAccess n, AArrayAccess n' -> n == n'
  | ANew t, ANew t' -> t == t'
  | ANewChannel, ANewChannel -> true
  | AIf, AIf -> true
  | AFind n, AFind n' -> n == n'
  | AOut(tl,t), AOut(tl',t') -> (t == t') && (equal_lists (==) tl tl')
  | AIn n, AIn n' -> n == n'
  | _ -> false
  
let rec equal_probaf p1 p2 =
  match p1, p2 with
    Proba(p, l), Proba(p',l') -> (p == p') && (equal_lists equal_probaf l l')
  | Count p, Count p' -> p == p'
  | OCount c, OCount c' -> c == c'
  | Cst f, Cst f' -> f = f'
  | Zero, Zero -> true
  | Card t, Card t' -> t == t'
  | AttTime, AttTime -> true
  | Time (n,p), Time (n',p') -> (n == n') && (equal_probaf p p')
  | ActTime(a,l), ActTime(a',l') -> (equal_action a a') && (equal_lists equal_probaf l l')
  | Add(p1,p2), Add(p1',p2') -> (equal_probaf p1 p1') && (equal_probaf p2 p2')
  | Mul(p1,p2), Mul(p1',p2') -> (equal_probaf p1 p1') && (equal_probaf p2 p2')
  | Sub(p1,p2), Sub(p1',p2') -> (equal_probaf p1 p1') && (equal_probaf p2 p2')
  | Div(p1,p2), Div(p1',p2') -> (equal_probaf p1 p1') && (equal_probaf p2 p2')
  | Max l, Max l' -> equal_lists equal_probaf l l'
  | Maxlength(n,t),Maxlength(n',t') -> (n == n') && (equal_terms t t')
  | TypeMaxlength(t),TypeMaxlength(t') -> t == t'
  | Length(f,l), Length(f',l') -> (f == f') && (equal_lists equal_probaf l l')
  | EpsFind, EpsFind -> true
  | EpsRand t, EpsRand t' -> t == t'
  | PColl1Rand t, PColl1Rand t' -> t == t'
  | PColl2Rand t, PColl2Rand t' -> t == t'
  | _ -> false

let equal_elsefind_facts (bl1,def_list1,t1) (bl2,def_list2,t2) =
  equal_lists (==) bl1 bl2 && 
  equal_def_lists def_list1 def_list2 && 
  equal_terms t1 t2

(* syntactic equality, possibly modulo associativity and commutativity,
   but no other equations *)

let rec dec_prod f t =
  match t.t_desc with
    FunApp(f',[t1;t2]) when f' == f ->
      (dec_prod f t1) @ (dec_prod f t2)
  | _ -> [t]

let rec synt_equal_terms t1 t2 =
  match (t1.t_desc, t2.t_desc) with
    Var(b1,l1),Var(b2,l2) ->
      (b1 == b2) && (List.for_all2 equal_terms l1 l2)
  | ReplIndex b1, ReplIndex b2 -> b1 == b2
  | FunApp(f1,[t1;t1']),FunApp(f2,[t2;t2']) when f1 == f2 && f1.f_eq_theories = Commut ->
      (* Commutative function symbols *)
      ((synt_equal_terms t1 t2) && (synt_equal_terms t1' t2')) ||
      ((synt_equal_terms t1 t2') && (synt_equal_terms t1' t2))
  | FunApp(f1,[_;_]),FunApp(f2,[_;_]) when f1 == f2 && 
      f1.f_eq_theories != NoEq && f1.f_eq_theories != Commut ->
      (* f1 is a binary function with an equational theory that is
	 not commutativity nor inverse -> it is a product-like function *)
	begin
	  let l1 = dec_prod f1 t1 in
	  let l2 = dec_prod f1 t2 in
	  match f1.f_eq_theories with 
	    NoEq | Commut -> Parsing_helper.internal_error "Terms.synt_equal_terms: cases NoEq, Commut should have been eliminated"
	  | AssocCommut | AssocCommutN _ | CommutGroup _ | ACUN _ ->
	      (* Commutative equational theories: test equality up to ordering *)
	      (List.length l1 == List.length l2) &&
	      (equal_up_to_order synt_equal_terms l1 l2)
	  | Assoc | AssocN _ | Group _  ->
	      (* Non-commutative equational theories: test equality in the same order *)
	      equal_lists synt_equal_terms l1 l2		
	end
  | FunApp(f1,l1),FunApp(f2,l2) ->
      (f1 == f2) && (List.for_all2 synt_equal_terms l1 l2)
  | TestE(t1,t2,t3), TestE(t1',t2',t3') ->
      (synt_equal_terms t1 t1') && (synt_equal_terms t2 t2') && (synt_equal_terms t3 t3')
  | FindE(l,t3,find_info),FindE(l',t3',find_info') ->
      (* Could do modulo renaming of bl and bl'! *)
      (equal_lists (fun (bl,def_list,t1,t2) (bl',def_list',t1',t2') ->
	(equal_lists (fun (b1,b2) (b1', b2') -> (b1 == b1') && (b2 == b2')) bl bl') && 
	(equal_def_lists def_list def_list') && 
	(synt_equal_terms t1 t1') && (synt_equal_terms t2 t2')) l l') && 
      (synt_equal_terms t3 t3') &&
      (find_info == find_info')
  | LetE(pat, t1, t2, topt), LetE(pat', t1', t2', topt') ->
      (synt_equal_pats pat pat') &&
      (synt_equal_terms t1 t1') &&
      (synt_equal_terms t2 t2') &&
      (match topt, topt' with
	None, None -> true
      |	Some t3, Some t3' -> synt_equal_terms t3 t3'
      |	_ -> false)
  | ResE(b,t), ResE(b',t') ->
      (b == b') && (synt_equal_terms t t')
  | EventAbortE(f), EventAbortE(f') -> 
      f == f'
  | _ -> false

and synt_equal_pats p1 p2 =
  match p1,p2 with
    PatVar b, PatVar b' -> b == b'
  | PatTuple (f,l), PatTuple (f',l') -> (f == f') && (List.for_all2 synt_equal_pats l l')
  | PatEqual t, PatEqual t' -> synt_equal_terms t t'
  | _ -> false


(* Compute a product *)

let rec make_prod prod = function
    [] -> 
      begin
	(* Look for the neutral element of the product *)
	match prod.f_eq_theories with
	  Group(_,_,n) | CommutGroup(_,_,n) | AssocN(_,n) 
	| AssocCommutN(_,n) | ACUN(_,n) -> 
	    build_term_type (snd n.f_type) (FunApp(n, []))
	| _ -> 
	    Parsing_helper.internal_error "Empty product impossible without a neutral element"
      end
  | [t] -> t
  | t::l -> build_term_type t.t_type (FunApp(prod, [t; make_prod prod l]))
  
(* [make_inv_prod eq_th l1 t l2] computes the product 
   inv (product (List.rev l1)) * t * inv(product l2) *)

let make_inv_prod eq_th l1 t l2 =
  match eq_th with
    ACUN(prod, neut) ->
      make_prod prod (l1 @ (t::l2))
  | Group(prod, inv, neut) | CommutGroup(prod, inv, neut) ->
      let compute_inv = compute_inv try_no_var_id (ref false) (prod, inv, neut) in
      let inv_rev_l1 = List.map compute_inv l1 in
      let inv_l2 = List.map compute_inv (List.rev l2) in
      make_prod prod (inv_rev_l1 @ (t :: inv_l2))
  | _ -> Parsing_helper.internal_error "No product in make_inv_prod"


(* [is_subterm t1 t2] returns [true] when [t1] is a subterm of [t2] *)

let rec is_subterm t1 t2 =
  if equal_terms t1 t2 then true else
  match t2.t_desc with
    Var(_,l) | FunApp(_,l) -> List.exists (is_subterm t1) l
  | ReplIndex _ -> false
  | _ -> Parsing_helper.internal_error "is_subterm only for Var/FunApp/ReplIndex terms"

(* Compute the length of the longest common prefix *)

let rec len_common_prefix l1 l2 =
  match (l1, l2) with
    [], _ | _, [] -> 0
  | (a1::l1,a2::l2) ->
      if equal_terms a1 a2 then 1 + len_common_prefix l1 l2 else 0

(* Compute the length of the longest common suffix *)

let len_common_suffix l1 l2 =
  len_common_prefix (List.rev l1) (List.rev l2)

(* Term from pattern *)

let rec term_from_pat = function
    PatVar b -> term_from_binder b
  | PatTuple (f,l) -> 
      build_term_type (snd f.f_type) (FunApp(f, List.map term_from_pat l))
  | PatEqual t -> t

(* Type of a pattern *)

let get_type_for_pattern = function
    PatVar b -> b.btype
  | PatTuple(f,_) -> snd f.f_type
  | PatEqual t -> t.t_type

(* Count the number of variables in a term *)

let rec list_add f = function
    [] -> 0
  | a::l -> f a + list_add f l

let rec count_var t =
  match t.t_desc with
    FunApp(f,l) -> list_add count_var l
  | Var _ -> 1
  | ReplIndex _ -> 0
  | _ -> Parsing_helper.internal_error "Only Var/FunApp/ReplIndex expected in count_var"

let rec size t =
  match t.t_desc with
    FunApp(_,l) | Var(_,l) -> list_add size l
  | ReplIndex _ -> 1
  | _ -> Parsing_helper.internal_error "Only Var/FunApp/ReplIndex expected in size"

(* New variable name *)

let vcounter = ref 0

let new_vname() =
  incr vcounter;
  !vcounter

let new_binder b0 =
  { sname = b0.sname;
    vname = new_vname();
    btype = b0.btype;
    args_at_creation = b0.args_at_creation;
    def = b0.def;
    link = NoLink;
    count_def = 0;
    root_def_array_ref = false;
    root_def_std_ref = false;
    array_ref = false;
    std_ref = false;
    count_array_ref = 0;
    count_exclude_array_ref = 0;
    priority = 0 }

let new_repl_index b0 =
  { ri_sname = b0.ri_sname;
    ri_vname = new_vname();
    ri_type = b0.ri_type;
    ri_link = NoLink }

let create_binder s n t a =
  { sname = s;
    vname = n;
    btype = t;
    args_at_creation = a;
    def = [];
    link = NoLink;
    count_def = 0;
    root_def_array_ref = false;
    root_def_std_ref = false;
    array_ref = false;
    std_ref = false;
    count_array_ref = 0;
    count_exclude_array_ref = 0;
    priority = 0 }

let create_repl_index s n t =
  { ri_sname = s;
    ri_vname = n;
    ri_type = t;
    ri_link = NoLink }

(* Create a term containing general variables that corresponds to a pattern *)

exception NonLinearPattern

let gvar_counter = ref 0
let gvar_name = "?x"

let create_gvar b = 
  incr gvar_counter;
  let b' = create_binder gvar_name (!gvar_counter) b.btype [] in
  let rec st_node = { above_node = st_node; 
		      binders = []; 
		      true_facts_at_def = []; 
		      def_vars_at_def = []; 
		      elsefind_facts_at_def = [];
		      future_binders = []; future_true_facts = []; 
		      definition = DGenVar;
		      definition_success = DGenVar} 
  in
  b'.def <- [st_node];
  b'

let gen_term_from_pat pat = 
  let rec gterm_from_pat = function
      PatVar b ->
	let b' = create_gvar b in
	if b.link != NoLink then raise NonLinearPattern;
	let bt = term_from_binder b' in
	link b (TLink bt);
	bt
    | PatTuple (f,l) -> 
	build_term_type (snd f.f_type) (FunApp(f, List.map gterm_from_pat l))
    | PatEqual t -> t
  in
  auto_cleanup (fun () -> gterm_from_pat pat)

let rec single_occ_gvar seen_list t = 
  match t.t_desc with
    Var (b,l) -> 
      if b.sname == gvar_name then
	begin
	  if List.memq b (!seen_list) then false else
	  begin
	    seen_list := b :: (!seen_list);
	    true
	  end
	end
      else
	List.for_all (single_occ_gvar seen_list) l
  | ReplIndex _ -> true
  | FunApp(_,l) -> List.for_all (single_occ_gvar seen_list) l
  | _ -> Parsing_helper.internal_error "Only Var/FunApp/ReplIndex expected in single_occ_gvar"



(* Find out whether a term is a conjunction of "defined(...)" conditions *)

let mem_binderref br l = List.exists (equal_binderref br) l

let add_binderref a accu =
  if mem_binderref a (!accu) then () else accu := a :: (!accu)

let setminus_binderref s1 s2 =
  List.filter (fun br -> not (mem_binderref br s2)) s1

let inter_binderref s1 s2 =
  List.filter (fun br -> mem_binderref br s2) s1

let union_binderref s1 s2 = 
  s2 @ (setminus_binderref s1 s2)

(* get def_list subterms *)

let rec get_deflist_subterms accu t =
  match t.t_desc with
    Var(b,l) -> add_binderref (b,l) accu
  | ReplIndex i -> ()
  | FunApp(f,l) -> List.iter (get_deflist_subterms accu) l
	(* The cases TestE, FindE, LetE, RestE, EventAbortE are probably not used *)
  | TestE(t1,t2,t3) -> 
      get_deflist_subterms accu t1;
      get_deflist_subterms accu t2;
      get_deflist_subterms accu t3
  | FindE(l0,t3, find_info) ->
      List.iter (fun (bl, def_list, t, t1) ->
	get_deflist_subterms accu t;
	get_deflist_subterms accu t1
	) l0;
      get_deflist_subterms accu t3
  | LetE(pat,t1,t2,topt) ->
      get_def_list_pat accu pat;
      get_deflist_subterms accu t1;
      get_deflist_subterms accu t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> get_deflist_subterms accu t3
      end
  | ResE(b,t) -> get_deflist_subterms accu t
  | EventAbortE f -> ()

and get_def_list_pat accu = function
    PatVar _ -> ()
  | PatTuple(f,l) -> List.iter (get_def_list_pat accu) l
  | PatEqual t -> get_deflist_subterms accu t

(* Change the occurrences and make sure nodes associated with Find
   are distinct for different occurrences of Find *)

let rec move_occ_term t = 
  let x_occ = new_occ() in
  let desc = 
    match t.t_desc with
	Var(b,l) -> Var(b, List.map move_occ_term l)
      |	ReplIndex i -> ReplIndex i
      |	FunApp(f,l) -> FunApp(f, List.map move_occ_term l)
      |	TestE(t1,t2,t3) -> 
	  let t1' = move_occ_term t1 in
	  let t2' = move_occ_term t2 in
	  let t3' = move_occ_term t3 in 
	  TestE(t1', t2', t3')
      |	FindE(l0,t3, find_info) -> 
	  let l0' = List.map (fun (bl,def_list,t1,t2) ->
	    let def_list' = List.map move_occ_br def_list in
	    let t1' = move_occ_term t1 in
	    let t2' = move_occ_term t2 in
	    (bl, def_list', t1', t2')) l0
	  in
	  let t3' = move_occ_term t3 in
	  FindE(l0', t3', find_info)
      |	LetE(pat, t1, t2, topt) ->
	  let pat' = move_occ_pat pat in
	  let t1' = move_occ_term t1 in
	  let t2' = move_occ_term t2 in
	  let topt' = match topt with
		 None -> None
	       | Some t3 -> Some (move_occ_term t3)
	  in
	  LetE(pat', t1', t2', topt')
      |	ResE(b,t) ->
	  ResE(b, move_occ_term t)
      |	EventAbortE f -> EventAbortE f 
  in
  { t_desc = desc;
    t_type = t.t_type;
    t_occ = x_occ;
    t_max_occ = !occ;
    t_loc = Parsing_helper.dummy_ext;
    t_incompatible = map_empty;
    t_facts = None }

and move_occ_pat = function
    PatVar b -> PatVar b
  | PatTuple (f,l) -> PatTuple(f,List.map move_occ_pat l)
  | PatEqual t -> PatEqual(move_occ_term t)

and move_occ_br (b,l) = (b, List.map move_occ_term l)

let rec move_occ_process p = 
  let x_occ = new_occ() in
  let desc = 
    match p.i_desc with
	Nil -> Nil
      | Par(p1,p2) -> 
	  let p1' = move_occ_process p1 in
	  let p2' = move_occ_process p2 in
	  Par(p1', p2')
      | Repl(b,p) -> Repl(b, move_occ_process p)
      | Input((c,tl),pat,p) ->
	  let tl' = List.map move_occ_term tl in
	  let pat' = move_occ_pat pat in
	  let p' = move_occ_oprocess p in
	  Input((c, tl'), pat', p')
  in
  { i_desc = desc;
    i_occ = x_occ; 
    i_max_occ = !occ;
    i_incompatible = map_empty; 
    i_facts = None }

and move_occ_oprocess p =
  let x_occ = new_occ() in
  let desc = 
    match p.p_desc with
	Yield -> Yield
      |	EventAbort f -> EventAbort f
      | Restr(b,p) -> Restr(b, move_occ_oprocess p)
      | Test(t,p1,p2) -> 
	  let t' = move_occ_term t in
	  let p1' = move_occ_oprocess p1 in
	  let p2' = move_occ_oprocess p2 in
	  Test(t', p1', p2')
      | Find(l0, p2, find_info) -> 
	  let l0' = List.map (fun (bl, def_list, t, p1) -> 
	    let def_list' = List.map move_occ_br def_list in
	    let t' = move_occ_term t in
	    let p1' = move_occ_oprocess p1 in
	    (bl, def_list', t', p1')) l0
	  in
	  let p2' = move_occ_oprocess p2 in
	  Find(l0', p2', find_info)
      | Let(pat,t,p1,p2) ->
	  let pat' = move_occ_pat pat in
	  let t' = move_occ_term t in
	  let p1' = move_occ_oprocess p1 in
	  let p2' = move_occ_oprocess p2 in	  
	  Let(pat', t', p1', p2')
      | Output((c,tl),t2,p) ->
	  let tl' = List.map move_occ_term tl in
	  let t2' = move_occ_term t2 in
	  let p' = move_occ_process p in
	  Output((c, tl'), t2', p')
      | EventP(t,p) ->
	  let t' = move_occ_term t in
	  let p' = move_occ_oprocess p in
	  EventP(t', p')
      | Get(tbl,patl,topt,p1,p2) -> 
	  let patl' = List.map move_occ_pat patl in
	  let topt' = 
	    match topt with 
	      Some t -> Some (move_occ_term t) 
	    | None -> None
	  in
	  let p1' = move_occ_oprocess p1 in
	  let p2' = move_occ_oprocess p2 in	  
          Get(tbl,patl',topt',p1', p2')
      | Insert (tbl,tl,p) -> 
	  let tl' = List.map move_occ_term tl in
	  let p' = move_occ_oprocess p in
          Insert(tbl, tl', p')
  in
  { p_desc = desc;
    p_occ = x_occ;
    p_max_occ = !occ;
    p_incompatible = map_empty; 
    p_facts = None }

let move_occ_process p =
  occ := 0;
  move_occ_process p

(* Copy a term
   Preserves occurrences of the original term. This is useful so that
   we can designate variables by occurrences in simplify coll_elim;
   otherwise, occurrences would be modified before they are tested.

   Several transformations are possible
 *)

type copy_transf =
    Links_RI (* Substitutes replication indices that are linked *)
  | Links_Vars 
     (* Substitutes variables that are linked, when their arguments are args_at_creation
	The linked variables are supposed to be defined above the copied terms/processes *)
  | Links_RI_Vars (* Combines Links_RI and Links_Vars *)
  | OneSubst of binder * term * bool ref 
     (* OneSubst(b,t,changed) substituted b[b.args_at_creation] with t.
	Sets changed to true when such a substitution has been done.
	b is assumed to be defined above the copied terms/processes *) 
  | OneSubstArgs of binderref * term 
     (* OneSubstArgs(br,t) substitutes t for the accesses br.
	It is assumed that br and t are already guaranteed to be defined,
	so br is removed from defined conditions if it occurs. *)
  | Rename of term list * binder * binder
     (* Rename(args, b, b') replaces array accesses b[args] with b'[args] *)
  | Links_Vars_Args of (binder * binder) list
     (* Links_Vars_Args(replacement_def_list) substitutes variables that are 
	linked, for any arguments: if b is linked to M, b[l] is
	replaced with M{l/b.args_at_creation}. replacement_def_list defines
	variable replacements to do in defined conditions. *)

(* Helper function for copy_def_list in case Links_Vars_Args *)

let rec get_remassign_subterms accu (b,l) =
  List.iter (get_remassign_terms accu) l;
  match b.link with
    NoLink -> ()
  | TLink _ -> add_binderref (b,l) accu

and get_remassign_terms accu t =
  match t.t_desc with
    Var(b,l) -> get_remassign_subterms accu (b,l)
  | ReplIndex(b) -> ()
  | FunApp(f,l) -> List.iter (get_remassign_terms accu) l
  | _ -> Parsing_helper.internal_error "if/let/find forbidden in defined conditions of find"

(* Copy functions *)

let rec copy_binder transf (b,l) =
  match transf with
    Rename(cur_array, b0, b0') ->
      let l' = List.map (copy_term transf) l in
      if (b == b0) && (List.for_all2 equal_terms l cur_array) then
	(b0', l')
      else
	(b,l')
  | _ -> 
      Parsing_helper.internal_error "copy_binder allowed only with transformation Rename"

and copy_term transf t = 
  match t.t_desc with
    ReplIndex b -> 
      begin
	match transf with
	  Links_Vars | OneSubst _ | OneSubstArgs _ | Rename _ | Links_Vars_Args _ -> t
	| Links_RI | Links_RI_Vars -> 
	    match b.ri_link with
	      NoLink -> t
	    | TLink t' -> move_occ_term t' (* Same comment as in case OneSubst *)
      end
  | Var(b,l) ->
      begin
        match transf with
          OneSubst(b',t',changed) ->
            if (b == b') && (is_args_at_creation b l) then
	      begin
		changed := true;
                move_occ_term t' (* This just makes a copy of the same term -- This is needed
				    to make sure that all terms are physically distinct,
				    which is needed to store facts correctly in
				    [Terms.build_def_process]. *)
	      end
            else
	      build_term2 t (Var(b,List.map (copy_term transf) l))
	| OneSubstArgs((b',l'), t') ->
	    if (b == b') && (List.for_all2 equal_terms l l') then
	      move_occ_term t' (* Same comment as in case OneSubst *)
	    else
	      build_term2 t (Var(b,List.map (copy_term transf) l))
	| Rename _ ->
	    let (b',l') = copy_binder transf (b,l) in
	    build_term2 t (Var(b',l'))
	| Links_Vars_Args _ -> 
	    begin
	      let l' = List.map (copy_term transf) l in
	      match b.link with
		NoLink -> build_term2 t (Var(b,l'))
	      | TLink t ->
		  let t = copy_term transf t in
                  (* Rename array indices *)
		  subst b.args_at_creation l' t
	    end
	| Links_RI ->  build_term2 t (Var(b,List.map (copy_term transf) l))
	| Links_Vars | Links_RI_Vars ->
	    match b.link with
	      TLink t' when is_args_at_creation b l -> move_occ_term t' (* Same comment as in case OneSubst *)
	    | _ -> build_term2 t (Var(b,List.map (copy_term transf) l))
      end
  | FunApp(f,l) ->
      build_term2 t (FunApp(f, List.map (copy_term transf) l))
  | TestE(t1,t2,t3) ->
      build_term2 t (TestE(copy_term transf t1,
				 copy_term transf t2, 
				 copy_term transf t3))
  | LetE(pat, t1, t2, topt) ->
      let pat' = copy_pat transf pat in
      let t1' = copy_term transf t1 in
      let t2' = copy_term transf t2 in
      let topt' = match topt with
	None -> None
      |	Some t3 -> Some (copy_term transf t3)
      in
      build_term2 t (LetE(pat', t1', t2', topt'))
  | FindE(l0, t3, find_info) -> 
      let l0' = List.map (fun (bl, def_list, t1, t2) ->
	(bl,
	 copy_def_list transf def_list,
	 copy_term transf t1,
	 copy_term transf t2)) l0
      in
      build_term2 t (FindE(l0', copy_term transf t3, find_info))
  | ResE(b,t) ->
      build_term2 t (ResE(b, copy_term transf t))
  | EventAbortE(f) ->
      Parsing_helper.internal_error "Event should have been expanded"

and copy_def_list transf def_list =
  match transf with
    OneSubst(b',t',changed) ->
      (* When removing assignments in_scope_only, and I am removing
         assignments on b, I know that b is in scope, so
         b[b.args_at_creation] is always defined, and I can remove that
         defined condition *)
      List.map (fun (b,l) ->
        (b, List.map (copy_term transf) l)) 
       (List.filter (fun (b,l) ->
          not ((b == b') && (is_args_at_creation b l))) def_list)
  | OneSubstArgs((b',l'), t') ->
      List.map (fun (b,l) ->
        (b, List.map (copy_term transf) l)) 
       (List.filter (fun (b,l) ->
          not ((b == b') && (List.for_all2 equal_terms l l'))) def_list)
  | Rename _ ->
      List.map (copy_binder transf) def_list
  | Links_Vars_Args(replacement_def_list) ->
      (* Update def_list, following removal of assignments *)
      (* 1: root_remassign = subterms of def_list whose root is
         a variable on which we remove assignments *)
      let root_remassign = ref [] in
      List.iter (get_remassign_subterms root_remassign) def_list;
      (* 2: not_root_remassign = elements of def_list whose root is
         not a variable on which we remove assignments *)
      let not_root_remassign =
	List.filter (fun (b,l) ->
	  match b.link with
	    NoLink -> true
	  | TLink _ -> false
	      ) def_list 
      in
      (* 3: compute the new def_list *)
      let accu = ref 
	  (List.map (fun (b,l) -> (b, List.map (copy_term transf) l)) 
	     ((!root_remassign) @ not_root_remassign))
      in
      List.iter (fun br -> get_deflist_subterms accu
	(copy_term transf (term_from_binderref br))) (!root_remassign);
      (* 4: replace defined(b) with defined(b') when b was used
	 only in defined conditions and it is defined when b' is defined *)
      List.map (fun (b,l) ->
	try 
	  (List.assq b replacement_def_list, l)
	with Not_found ->
	  (b,l)) (!accu)
  | Links_RI -> List.map (fun (b,l) -> (b, List.map (copy_term transf) l)) def_list
  | Links_Vars | Links_RI_Vars ->
      (* When we substitute b (b.link != NoLink), we know that b is in scope, so
	 we can remove the condition that b is defined. *)
      List.map (fun (b,l) ->
        (b, List.map (copy_term transf) l)) 
       (List.filter (fun (b,l) ->
          not ((b.link != NoLink) && (is_args_at_creation b l))) def_list)
      
and copy_pat transf = function
  PatVar b -> PatVar b
| PatTuple (f,l) -> PatTuple(f,List.map (copy_pat transf) l)
| PatEqual t -> PatEqual(copy_term transf t)

(* Compute term { l / cur_array } *)

and subst cur_array l term =
  List.iter2 (fun b t -> b.ri_link <- (TLink t)) cur_array l;
  let term' = copy_term Links_RI term in
  List.iter (fun b -> b.ri_link <- NoLink) cur_array;
  term'


let rec copy_process transf p = 
  iproc_from_desc3 p (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) ->
      Par(copy_process transf p1,
	  copy_process transf p2)
  | Repl(b,p) ->
      Repl(b, copy_process transf p)
  | Input((c,tl), pat, p) ->
      Input((c, List.map (copy_term transf) tl),
	    copy_pat transf pat,
	    copy_oprocess transf p))

and copy_oprocess transf p =
  oproc_from_desc3 p (
  match p.p_desc with
    Yield -> Yield
  | EventAbort f -> EventAbort f
  | Restr(b, p) ->
      Restr(b, copy_oprocess transf p)
  | Test(t,p1,p2) ->
      Test(copy_term transf t, 
	   copy_oprocess transf p1,
           copy_oprocess transf p2)
  | Let(pat, t, p1, p2) ->
      Let(copy_pat transf pat, 
	  copy_term transf t, 
	  copy_oprocess transf p1,
          copy_oprocess transf p2)
  | Output((c,tl),t2,p) ->
      Output((c, List.map (copy_term transf) tl),
	     copy_term transf t2,
	     copy_process transf p)
  | Find(l0, p2, find_info) ->
      let l0' = List.map (fun (bl, def_list, t, p1) ->
	(bl, 
	 copy_def_list transf def_list, 
	 copy_term transf t,
	 copy_oprocess transf p1)) l0 in
      Find(l0', copy_oprocess transf p2, find_info)
  | EventP(t,p) ->
      EventP(copy_term transf t, 
	     copy_oprocess transf p)
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  )

(* Compute element{l/cur_array}, where element is def_list, simp_facts
   Similar to what subst does for terms. *)

let subst_def_list cur_array l def_list =
  List.iter2 (fun b t -> b.ri_link <- (TLink t)) cur_array l;
  let def_list' = copy_def_list Links_RI def_list in
  List.iter (fun b -> b.ri_link <- NoLink) cur_array;
  def_list'

let subst_else_find cur_array l (bl, def_list, t) =
  List.iter2 (fun b t -> if not (List.memq b bl) then b.ri_link <- (TLink t)) cur_array l;
  let def_list' = copy_def_list Links_RI def_list in
  let t' = copy_term Links_RI t in
  List.iter (fun b -> if not (List.memq b bl) then b.ri_link <- NoLink) cur_array;
  (bl, def_list', t')

let subst_simp_facts cur_array l (substs, facts, elsefind) =
  (List.map (subst cur_array l) substs,
   List.map (subst cur_array l) facts,
   List.map (subst_else_find cur_array l) elsefind)


(* Substitution of v[v.args_at_creation] only
   Preserves occurrences of the original term. This is useful so that
   we can designate variables by occurrences in simplify coll_elim;
   otherwise, occurrences would be modified before they are tested. *)

let subst3 subst t =
  auto_cleanup (fun () ->
    List.iter (fun (b,t') -> link b (TLink t')) subst;
    copy_term Links_Vars t)

let subst_def_list3 subst def_list =
  auto_cleanup (fun () ->
    List.iter (fun (b,t') -> link b (TLink t')) subst;
    copy_def_list Links_Vars def_list)

let subst_oprocess3 subst p =
  auto_cleanup (fun () ->
    List.iter (fun (b,t') -> link b (TLink t')) subst;
    copy_oprocess Links_Vars p)

(* [find_some f l] returns [f a] for the first element
   [a] of the list [l] such that [f a <> None].
   It returns [None] if [f a = None] for all [a] in [l]. *)

let rec find_some f = function
    [] -> None
  | a::l ->
      match f a with
	None -> find_some f l
      |	x -> x

(* [replace l1 l0 t] replaces all terms in [l1] with the 
   corresponding term in [l0] inside [t] *)

let rec assoc l1 l0 t =
  match l1, l0 with
    [], [] -> raise Not_found
  | a1::l1, a0::l0 ->
      if equal_terms a1 t then a0 else assoc l1 l0 t
  | _ ->
      Parsing_helper.internal_error "Lists should have the same length in Terms.assoc"
    
let rec replace l1 l0 t =
  try
    assoc l1 l0 t
  with Not_found ->
    match t.t_desc with
      FunApp(f,l) ->
	build_term2 t (FunApp(f, List.map (replace l1 l0) l))
    | ReplIndex _ -> t
    | Var(b,l) ->
	build_term2 t (Var(b, List.map (replace l1 l0) l))
    | _ -> Parsing_helper.internal_error "Var/Fun/ReplIndex expected in Terms.replace"

(* Check whether a term t refers to a binder b0 *)

let no_def = ref false

let rec refers_to b0 t = 
  match t.t_desc with
    Var (b,l) -> 
      (b == b0) || (List.exists (refers_to b0) l) ||
      (match b.link with
	 TLink t -> refers_to b0 t
       | _ -> false)
  | FunApp(f,l) -> List.exists (refers_to b0) l
  | ReplIndex i -> false
  | TestE(t1,t2,t3) -> (refers_to b0 t1) || (refers_to b0 t2) || (refers_to b0 t3)
  | ResE(b,t) -> refers_to b0 t
  | EventAbortE f -> false
  | FindE(l0,t3, find_info) -> 
      (List.exists (fun (bl,def_list,t1,t2) ->
	(List.exists (refers_to_br b0) def_list) ||
	(refers_to b0 t1) || (refers_to b0 t2)) l0) || 
      (refers_to b0 t3)
  | LetE(pat, t1, t2, topt) ->
      (refers_to_pat b0 pat) ||
      (refers_to b0 t1) || (refers_to b0 t2) ||
      (match topt with
	None -> false
      |	Some t3 -> refers_to b0 t3)

and refers_to_br b0 (b,l) =
  ((not (!no_def)) && (b == b0)) || List.exists (refers_to b0) l

and refers_to_pat b0 = function
    PatVar b -> false
  | PatTuple (f,l) -> List.exists (refers_to_pat b0) l
  | PatEqual t -> refers_to b0 t 

let rec refers_to_process b0 p = 
  match p.i_desc with
    Nil -> false
  | Par(p1,p2) -> (refers_to_process b0 p1) || (refers_to_process b0 p2)
  | Repl(b,p) -> refers_to_process b0 p
  | Input((c,tl),pat,p) -> 
      (List.exists (refers_to b0) tl) || (refers_to_pat b0 pat) || (refers_to_oprocess b0 p)

and refers_to_oprocess b0 p =
  match p.p_desc with
    Yield | EventAbort _ -> false
  | Restr(b,p) -> refers_to_oprocess b0 p
  | Test(t,p1,p2) -> (refers_to b0 t) || (refers_to_oprocess b0 p1) ||
    (refers_to_oprocess b0 p2)
  | Find(l0,p2, find_info) ->
      (List.exists (fun (bl,def_list,t,p1) ->
	(List.exists (refers_to_br b0) def_list) ||
        (refers_to b0 t) || (refers_to_oprocess b0 p1)) l0) || 
      (refers_to_oprocess b0 p2)
  | Output((c,tl),t2,p) ->
      (List.exists (refers_to b0) tl) || (refers_to b0 t2) || (refers_to_process b0 p)
  | EventP(t,p) ->
      (refers_to b0 t) || (refers_to_oprocess b0 p)
  | Let(pat,t,p1,p2) ->
      (refers_to b0 t) || (refers_to_pat b0 pat) || 
      (refers_to_oprocess b0 p1) ||(refers_to_oprocess b0 p2)
  | Get(tbl,patl,topt,p1,p2) ->
      (List.exists (refers_to_pat b0) patl) || 
      (match topt with None -> false | Some t -> refers_to b0 t) || 
      (refers_to_oprocess b0 p1) ||(refers_to_oprocess b0 p2)
  | Insert(tbl,tl,p) ->
      (List.exists (refers_to b0) tl) || (refers_to_oprocess b0 p)

let rec refers_to_fungroup b = function
    ReplRestr(_,_,funlist) ->
      List.exists (refers_to_fungroup b) funlist
  | Fun(_,_,res,_) -> refers_to b res

let refers_to_nodef b0 t =
  no_def := true;
  let res = refers_to b0 t in
  no_def := false;
  res

let refers_to_process_nodef b0 p =
  no_def := true;
  let res = refers_to_oprocess b0 p in
  no_def := false;
  res

(* Extract defined variables from a pattern *)

let rec vars_from_pat accu = function
    PatVar b -> b::accu
  | PatEqual t -> accu
  | PatTuple (f,l) -> vars_from_pat_list accu l

and vars_from_pat_list accu = function
    [] -> accu
  | (a::l) -> vars_from_pat_list (vars_from_pat accu a) l


(* Test if a variable occurs in a pattern *)

let rec occurs_in_pat b = function
    PatVar b' -> b' == b
  | PatTuple (f,l) -> List.exists (occurs_in_pat b) l
  | PatEqual t -> false

(* Testing boolean values *)

let is_true t =
  match t.t_desc with
    FunApp(f,[]) when f == Settings.c_true -> true
  | _ -> false

let is_false t =
  match t.t_desc with
    FunApp(f,[]) when f == Settings.c_false -> true
  | _ -> false

(* Applying boolean functions *)

let make_true () =
  build_term_type Settings.t_bool (FunApp(Settings.c_true, []))
  
let make_false () =
  build_term_type Settings.t_bool (FunApp(Settings.c_false, []))

let make_and_ext ext t t' =
  if (is_true t) || (is_false t') then t' else
  if (is_true t') || (is_false t) then t else
  new_term Settings.t_bool ext (FunApp(Settings.f_and, [t;t']))

let make_and t t' =  make_and_ext Parsing_helper.dummy_ext t t'

let make_or_ext ext t t' =
  if (is_false t) || (is_true t') then t' else
  if (is_false t') || (is_true t) then t else
  new_term Settings.t_bool ext (FunApp(Settings.f_or, [t;t']))

let make_or t t' =  make_or_ext Parsing_helper.dummy_ext t t'

let rec make_and_list = function
    [] -> make_true()
  | [a] -> a
  | (a::l) -> make_and a (make_and_list l)

let rec make_or_list = function
    [] -> make_false()
  | [a] -> a
  | (a::l) -> make_or a (make_or_list l)

let make_not t =
  build_term_type Settings.t_bool (FunApp(Settings.f_not, [t]))
  
let make_equal_ext ext t t' =
  new_term Settings.t_bool ext
    (FunApp(Settings.f_comp Equal t.t_type t'.t_type, [t;t']))

let make_equal t t' = make_equal_ext Parsing_helper.dummy_ext t t'

let make_let_equal t t' =
  build_term_type Settings.t_bool (FunApp(Settings.f_comp LetEqual t.t_type t'.t_type, [t;t']))

let make_diff_ext ext t t' =
  new_term Settings.t_bool ext
    (FunApp(Settings.f_comp Diff t.t_type t'.t_type, [t;t']))

let make_diff t t' = make_diff_ext Parsing_helper.dummy_ext t t'

let make_for_all_diff t t' =
  build_term_type Settings.t_bool (FunApp(Settings.f_comp ForAllDiff t.t_type t'.t_type, [t;t']))

(* Put a term in the form or (and (...)) *)

let rec get_or t =
  match t.t_desc with
    FunApp(f, [t1;t2]) when f == Settings.f_or ->
      (get_or t1) @ (get_or t2)
  | _ -> [t]

let rec make_and1 a = function
    [] -> Parsing_helper.internal_error "make_and1 empty"
  | [b] -> make_and b a
  | (b::l2) -> make_or (make_and a b) (make_and1 a l2)

let rec make_and2 l1 = function
    [] -> Parsing_helper.internal_error "make_and2 empty"
  | [a] -> make_and1 a l1
  | (a::l2) -> make_or (make_and1 a l1) (make_and2 l1 l2)

let make_and_distr t1 t2 =
  if (is_false t1) || (is_false t2) then make_false() else
  if is_true t1 then t2 else
  if is_true t2 then t1 else
  (* If t1 or t2 is "or", distribute *)
  make_and2 (get_or t1) (get_or t2)

let rec or_and_form t =
  match t.t_desc with
    FunApp(f, [t1;t2]) when f == Settings.f_and ->
      make_and_distr (or_and_form t1) (or_and_form t2)
  | FunApp(f, [t1;t2]) when f == Settings.f_or ->
      make_or (or_and_form t1) (or_and_form t2)
  | _ -> t

(* Test for tuples *)

let is_tuple t =
  match t.t_desc with
    FunApp(f, _) when (f.f_options land Settings.fopt_COMPOS) != 0 -> true
  | _ -> false

let is_pat_tuple = function
    PatTuple (f,_) -> true
  | _ -> false

(* Building lets *)

let rec put_lets l1 l2 p1 p2 = 
  match (l1,l2) with
    [],[] -> p1
  | (a1::l1),(a2::l2) ->
      oproc_from_desc (Let(a1, a2, put_lets l1 l2 p1 p2, p2))
  | _ -> Parsing_helper.internal_error "Different lengths in put_lets"

let rec put_lets_term l1 l2 p1 p2 = 
  match (l1,l2) with
    [],[] -> p1
  | (a1::l1),(a2::l2) ->
      build_term_type p1.t_type (LetE(a1, a2, put_lets_term l1 l2 p1 p2, p2))
  | _ -> Parsing_helper.internal_error "Different lengths in put_lets"

exception Impossible

let rec split_term f0 t = 
  match t.t_desc with
    Var(_,_) -> 
      (* TO DO when the variable is created by a restriction,
         it is different from a tuple with high probability *)
      raise Not_found
  | ReplIndex i -> 
      (* A replication index cannot occur because the split term must be of a bitstring type *)
      Parsing_helper.internal_error "A replication index should not occur in Terms.split_term"
  | FunApp(f,l) when f == f0 -> l
  | FunApp(f,l) -> 
      if f0.f_cat == Tuple && (f.f_cat == Tuple || (f.f_cat == Std && l == [] && (!Settings.constants_not_tuple))) then
	raise Impossible
      else
	raise Not_found
  | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ ->
      Parsing_helper.internal_error "If, find, let, new, and event should have been expanded (Simplify)"


  
(* Empty tree of definition dependances 
   The treatment of TestE/FindE/LetE/ResE is necessary: build_def_process
   is called in check.ml.
*)


let rec empty_def_term t =
  t.t_facts <- None;
  match t.t_desc with
    Var(b,l) ->
      b.def <- [];
      empty_def_term_list l
  | ReplIndex _ -> ()
  | FunApp(_,l) ->
      empty_def_term_list l
  | TestE(t1,t2,t3) ->
      empty_def_term t2;
      empty_def_term t3;
      empty_def_term t1
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	List.iter (fun (b1,b2) -> b1.def <- []) bl;
	empty_def_term_def_list def_list;
	empty_def_term t1;
	empty_def_term t2) l0;
      empty_def_term t3;
  | LetE(pat, t1, t2, topt) ->
      empty_def_pattern pat;
      empty_def_term t1;
      empty_def_term t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> empty_def_term t3
      end
  | ResE(b,t) -> b.def <- []; empty_def_term t
  | EventAbortE _ -> ()

and empty_def_term_list l = List.iter empty_def_term l

and empty_def_br (b,l) = b.def <- []; empty_def_term_list l

and empty_def_term_def_list def_list = 
  List.iter empty_def_br def_list

and empty_def_pattern = function
    PatVar b -> b.def <- []
  | PatTuple (f,l) -> List.iter empty_def_pattern l
  | PatEqual t -> empty_def_term t

let rec empty_def_process p = 
  p.i_facts <- None;
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      empty_def_process p1;
      empty_def_process p2
  | Repl(b,p) ->
      empty_def_process p
  | Input((c,tl),pat,p) ->
      List.iter empty_def_term tl;
      empty_def_pattern pat;
      empty_def_oprocess p

and empty_def_oprocess p = 
  p.p_facts <- None;
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b,p) ->
      b.def <- [];
      empty_def_oprocess p
  | Test(t,p1,p2) ->
      empty_def_term t;
      empty_def_oprocess p1;
      empty_def_oprocess p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list,t,p1) ->
	List.iter (fun (b1,b2) -> b1.def <- []) bl;
	empty_def_term_def_list def_list;
	empty_def_term t;
	empty_def_oprocess p1) l0;
      empty_def_oprocess p2
  | Output((c,tl),t',p) ->
      List.iter empty_def_term tl;
      empty_def_term t';
      empty_def_process p
  | Let(pat,t,p1,p2) ->
      empty_def_term t;
      empty_def_pattern pat;
      empty_def_oprocess p1;
      empty_def_oprocess p2
  | EventP(t,p) ->
      empty_def_term t;
      empty_def_oprocess p
  | Get(tbl,patl,topt,p1,p2) ->
      List.iter empty_def_pattern patl;
      (match topt with None -> () | Some t -> empty_def_term t);
      empty_def_oprocess p1;
      empty_def_oprocess p2
  | Insert(tbl,tl,p) -> 
      List.iter empty_def_term tl;
      empty_def_oprocess p

(* Functions used for filtering elsefind facts *)

(* [not_deflist b elsefind] returns true when [b] does not occur
   in the "defined" conditions of [elsefind] *)

let not_deflist b (_, def_list, _) =
  not (List.exists (refers_to_br b) def_list)

(* [not_deflist_l bl elsefind] returns true when no variable in [bl] occurs
   in the "defined" conditions of [elsefind] *)

let not_deflist_l bl elsefind =
  List.for_all (fun b -> not_deflist b elsefind) bl

(* Check that a term is a basic term (no if/let/find/new/event) *)

let rec check_no_ifletfindres t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) ->
      List.for_all check_no_ifletfindres l
  | ReplIndex _ -> true
  | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ ->
      false

(* Build tree of definition dependences
   The treatment of TestE/FindE/LetE/ResE is necessary: build_def_process
   is called in check.ml.

   The value of elsefind_facts is correct even if the game has not been expanded:
   we correctly discard elsefind_facts when their defined condition refers
   to a variable defined in a term.
   We compute elsefind_facts only for processes. For terms, they
   would be useful only for non-expanded games, in which variables
   defined in terms may have array accesses. (In expanded games,
   variables can be defined in terms only in find conditions, and
   such variables cannot have array accesses.)
   *)

let rec close_def_subterm accu (b,l) =
  add_binderref (b,l) accu;
  List.iter (close_def_term accu) l

and close_def_term accu t =
  match t.t_desc with
    Var(b,l) -> close_def_subterm accu (b,l)
  | ReplIndex i -> ()
  | FunApp(f,l) -> List.iter (close_def_term accu) l
  | _ -> Parsing_helper.input_error "if/find/let forbidden in defined conditions of find" t.t_loc

let defined_refs_find bl def_list defined_refs =
  (* Compute the defined references in the condition *)
  let accu = ref defined_refs in
  List.iter (close_def_subterm accu) def_list;
  let defined_refs_cond = !accu in
  (* Compute the defined references in the then branch *)
  let vars = List.map fst bl in
  let repl_indices = List.map snd bl in
  let def_list' = subst_def_list repl_indices (List.map term_from_binder vars) def_list in
  let accu = ref ((List.map binderref_from_binder vars) @ defined_refs) in
  List.iter (close_def_subterm accu) def_list';
  let defined_refs_branch = !accu in
  (defined_refs_cond, defined_refs_branch)

let add_var accu b =
  if List.memq b accu then accu else b::accu

let rec unionq l1 = function
    [] -> l1
  | (a::l) -> 
      if List.memq a l1 then unionq l1 l else
      a::(unionq l1 l)

let rec add_vars_from_pat accu = function
    PatVar b -> add_var accu b
  | PatEqual t -> accu
  | PatTuple (f,l) -> add_vars_from_pat_list accu l

and add_vars_from_pat_list accu = function
    [] -> accu
  | (a::l) -> add_vars_from_pat_list (add_vars_from_pat accu a) l

let rec def_vars_term accu t = 
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> def_vars_term_list accu l
  | ReplIndex i -> accu
  | TestE(t1,t2,t3) -> 
      def_vars_term (def_vars_term (def_vars_term accu t1) t2) t3
  | FindE(l0, t3, _) ->
      let accu = ref (def_vars_term accu t3) in
      List.iter (fun (bl, def_list, t1, t2) ->
	(*Nothing to do for def_list: it contains only
          Var and Fun*)
	accu := unionq (List.map fst bl) (def_vars_term (def_vars_term (!accu) t1) t2)
	     ) l0;
      !accu
  | LetE(pat, t1, t2, topt) ->
      let accu' = match topt with
	None -> accu
      |	Some t3 -> def_vars_term accu t3 
      in
      def_vars_term (def_vars_pat (add_vars_from_pat (def_vars_term accu' t2) pat) pat) t1
  | ResE(b,t) ->
      add_var (def_vars_term accu t) b
  | EventAbortE _ -> accu

and def_vars_term_list accu = function
    [] -> accu
  | (a::l) -> def_vars_term (def_vars_term_list accu l) a

and def_vars_pat accu = function
    PatVar b -> accu 
  | PatTuple (f,l) -> def_vars_pat_list accu l
  | PatEqual t -> def_vars_term accu t

and def_vars_pat_list accu = function
    [] -> accu
  | (a::l) -> def_vars_pat (def_vars_pat_list accu l) a

(* def_term is always called with  above_node.def_vars_at_def \subseteq def_vars
def_term returns a node n'. In this node n', we always have n'.def_vars_at_def \subseteq def_vars
Same property for def_term_list, def_term_def_list, def_pattern, def_pattern_list.
By induction. 
In cases ReplIndex, FindE, n' = above_node. 
In the other cases, we use the induction hypothesis. *)

let rec def_term event_accu above_node true_facts def_vars t =
  if (t.t_facts != None) then
    Parsing_helper.internal_error "Two terms physically equal: cannot compute facts correctly";
  t.t_facts <- Some (true_facts, def_vars, above_node);
  match t.t_desc with
    Var(_,l) | FunApp(_,l) ->
      def_term_list event_accu above_node true_facts def_vars l
  | ReplIndex i -> above_node
  | TestE(t1,t2,t3) ->
      let true_facts' = t1 :: true_facts in
      let true_facts'' = (make_not t1) :: true_facts in
      ignore(def_term event_accu above_node true_facts' def_vars t2);
      ignore(def_term event_accu above_node true_facts'' def_vars t3);
      def_term event_accu above_node true_facts def_vars t1
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	let vars = List.map fst bl in
	let repl_indices = List.map snd bl in
	let t1' = subst repl_indices (List.map term_from_binder vars) t1 in
	let true_facts' =  t1' :: true_facts in
	let accu = ref def_vars in
	List.iter (close_def_subterm accu) def_list;
	let def_vars_t1 = !accu in
	let def_list' = subst_def_list repl_indices (List.map term_from_binder vars) def_list in
	let accu = ref def_vars in
	List.iter (close_def_subterm accu) def_list';
	let def_vars' = !accu in
	let above_node' = { above_node = above_node; binders = vars; 
			    true_facts_at_def = true_facts'; 
			    def_vars_at_def = def_vars';
			    elsefind_facts_at_def = [];
			    future_binders = []; future_true_facts = []; 
			    definition = DTerm t;
			    definition_success = DTerm t2 } 
	in
	List.iter (fun b -> b.def <- above_node' :: b.def) vars;
	ignore(def_term event_accu (def_term_def_list event_accu above_node true_facts def_vars def_list) true_facts def_vars_t1 t1);
	ignore(def_term event_accu above_node' true_facts' def_vars' t2)) l0;
      ignore(def_term event_accu above_node true_facts def_vars t3);
      above_node
  | LetE(pat, t1, t2, topt) ->
      let above_node' = def_term event_accu above_node true_facts def_vars t1 in
      let accu = ref [] in
      let above_node'' = def_pattern accu event_accu above_node' true_facts def_vars pat in
      let true_facts' = ((match pat with PatVar _ -> make_let_equal | _ -> make_equal) (term_from_pat pat) t1) :: true_facts in
      let above_node''' = { above_node = above_node''; binders = !accu; 
			    true_facts_at_def = true_facts'; 
			    def_vars_at_def = def_vars;
			    elsefind_facts_at_def = [];
			    future_binders = []; future_true_facts = []; 
			    definition = DTerm t;
			    definition_success = DTerm t2 } 
      in
      List.iter (fun b -> b.def <- above_node''' :: b.def) (!accu);
      ignore (def_term event_accu above_node''' true_facts' def_vars t2);
      begin
	match topt with
	  None -> ()
	| Some t3 -> 
	    let true_facts' = 
	      try
		(make_for_all_diff (gen_term_from_pat pat) t1) :: true_facts
	      with NonLinearPattern -> true_facts
	    in
	    ignore(def_term event_accu above_node' true_facts' def_vars t3)
      end;
      above_node'
  | ResE(b, t') ->
      let above_node' = { above_node = above_node; binders = [b]; 
			  true_facts_at_def = true_facts; 
			  def_vars_at_def = def_vars;
			  elsefind_facts_at_def = [];
			  future_binders = []; future_true_facts = []; 
			  definition = DTerm t;
			  definition_success = DTerm t' } 
      in
      b.def <- above_node' :: b.def;
      def_term event_accu above_node' true_facts def_vars t'
  | EventAbortE f ->
      begin
	match event_accu with
	  None -> ()
	| Some accu -> 
	    let idx = build_term_type Settings.t_bitstring (FunApp(Settings.get_tuple_fun [], [])) in
	    let t = build_term_type Settings.t_bool (FunApp(f, [idx])) in
	    accu := (t, Some (true_facts, def_vars, above_node)) :: (!accu)
      end;
      above_node
      

and def_term_list event_accu above_node true_facts def_vars = function
    [] -> above_node
  | (a::l) -> def_term_list event_accu (def_term event_accu above_node true_facts def_vars a) true_facts def_vars l

and def_term_def_list event_accu above_node true_facts def_vars = function
    [] -> above_node
  | (b,l)::l' -> def_term_def_list event_accu (def_term_list event_accu above_node true_facts def_vars l) true_facts def_vars l'

and def_pattern accu event_accu above_node true_facts def_vars = function
    PatVar b -> accu := b :: (!accu); above_node
  | PatTuple (f,l) -> def_pattern_list accu event_accu above_node true_facts def_vars l
  | PatEqual t -> def_term event_accu above_node true_facts def_vars t

and def_pattern_list accu event_accu above_node true_facts def_vars = function
    [] -> above_node 
  | (a::l) -> def_pattern_list accu event_accu (def_pattern accu event_accu above_node true_facts def_vars a) true_facts def_vars l

(* def_process is always called with above_node.def_vars_at_def \subseteq def_vars
   By induction, also using the properties of def_term, ...
   One case in which the two values are different is in the condition of find:
   def_vars contains the def_list, which is not included in above_node.def_vars_at_def. *)

let rec def_process event_accu above_node true_facts def_vars p' =
  if p'.i_facts != None then
    Parsing_helper.internal_error "Two processes physically equal: cannot compute facts correctly";
  p'.i_facts <- Some (true_facts, def_vars, above_node);
  match p'.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      def_process event_accu above_node true_facts def_vars p1;
      def_process event_accu above_node true_facts def_vars p2
  | Repl(b,p) ->
      (* A node is needed here, even if the replication defines no
	 binders, because I rely on the node to locate the
	 replication in Simplify.CompatibleDefs.check_compatible *)
      let above_node' = { above_node = above_node; binders = [];
                          true_facts_at_def = true_facts;
                          def_vars_at_def = def_vars;
                          elsefind_facts_at_def = [];
                          future_binders = []; future_true_facts = []; 
                          definition = DInputProcess p';
			  definition_success = DInputProcess p }
      in
      def_process event_accu above_node' true_facts def_vars p
  | Input((c,tl),pat,p) ->
      let above_node' = def_term_list event_accu above_node true_facts def_vars tl in
      let accu = ref [] in
      let above_node'' = def_pattern accu event_accu above_node' true_facts def_vars pat in
      (* is_find_unique uses this node to test whether two variables are defined
	 in the same input/output block, so it's important to generate this
	 node even if the pattern pat defines no variable. *)
      let above_node''' = { above_node = above_node''; binders = !accu; 
			    true_facts_at_def = true_facts; 
			    def_vars_at_def = def_vars;
			    elsefind_facts_at_def = [];
			    future_binders = []; future_true_facts = []; 
			    definition = DInputProcess p';
			    definition_success = DProcess p } 
      in
      List.iter (fun b -> b.def <- above_node''' :: b.def) (!accu);
      let (fut_binders, fut_true_facts) = 
	def_oprocess event_accu above_node''' true_facts def_vars [] p
      in
      above_node'''.future_binders <- fut_binders;
      above_node'''.future_true_facts <- fut_true_facts

and def_oprocess event_accu above_node true_facts def_vars elsefind_facts p' =
  if p'.p_facts != None then
    Parsing_helper.internal_error "Two processes physically equal: cannot compute facts correctly";
  p'.p_facts <- Some (true_facts, def_vars, above_node);
  match p'.p_desc with
    Yield -> 
      ([],[])
  | EventAbort f -> 
      begin
	match event_accu with
	  None -> ()
	| Some accu -> 
	    let idx = build_term_type Settings.t_bitstring (FunApp(Settings.get_tuple_fun [], [])) in
	    let t = build_term_type Settings.t_bool (FunApp(f, [idx])) in
	    accu := (t, Some (true_facts, def_vars, above_node)) :: (!accu)
      end;
      ([],[])
  | Restr(b,p) ->
      let elsefind_facts' = List.filter (not_deflist b) elsefind_facts in
      let above_node' = { above_node = above_node; binders = [b]; 
			  true_facts_at_def = true_facts; 
			  def_vars_at_def = def_vars;
			  elsefind_facts_at_def = elsefind_facts;
			  future_binders = []; future_true_facts = []; 
			  definition = DProcess p';
			  definition_success = DProcess p } 
      in
      b.def <- above_node' :: b.def;
      let (fut_binders, fut_true_facts) = 
	def_oprocess event_accu above_node' true_facts def_vars elsefind_facts' p
      in
      above_node'.future_binders <- fut_binders;
      above_node'.future_true_facts <- fut_true_facts;
      (b::fut_binders, fut_true_facts)
  | Test(t,p1,p2) ->
      let above_node' = def_term event_accu above_node true_facts def_vars t in
      let true_facts' = t :: true_facts in
      let true_facts'' = (make_not t) :: true_facts in
      let vars_t = def_vars_term [] t in
      let elsefind_facts' = List.filter (not_deflist_l vars_t) elsefind_facts in
      let (fut_binders1, fut_true_facts1) = 
	def_oprocess event_accu above_node' true_facts' def_vars elsefind_facts' p1
      in
      let (fut_binders2, fut_true_facts2) = 
	def_oprocess event_accu above_node' true_facts'' def_vars elsefind_facts' p2
      in
      (intersect (==) fut_binders1 fut_binders2, 
       intersect equal_terms fut_true_facts1 fut_true_facts2)
  | Find(l0,p2,_) ->
      let l0_conds = List.map (fun (bl,def_list,t1,_) -> (List.map snd bl,def_list,t1)) l0 in
      let l0_elsefind = List.filter (function (_,_,t) -> check_no_ifletfindres t) l0_conds in 
      let elsefind_facts' = l0_elsefind @ elsefind_facts in
      let (fut_binders2, fut_true_facts2) = 
	def_oprocess event_accu above_node true_facts def_vars elsefind_facts' p2
      in
      let rec find_l = function
	  [] -> (fut_binders2, fut_true_facts2)
	| (bl,def_list,t,p1)::l ->
	    let (fut_bindersl, fut_true_factsl) = find_l l in
	    let vars = List.map fst bl in
	    let repl_indices = List.map snd bl in
            (* The variables defined in t are variables defined in conditions of find,
	       one cannot make array accesses to them, nor test their definition,
	       so they will not appear in defined conditions of elsefind_facts.
	       We need not take them into account to update elsefind_facts. *)
	    let elsefind_facts'' = List.filter (not_deflist_l vars) elsefind_facts in
	    let t' = subst repl_indices (List.map term_from_binder vars) t in
	    let true_facts' = t' :: true_facts in
	    let accu = ref def_vars in
	    List.iter (close_def_subterm accu) def_list;
	    let def_vars_t = !accu in
	    let def_list' = subst_def_list repl_indices (List.map term_from_binder vars) def_list in
	    let accu = ref def_vars in
	    List.iter (close_def_subterm accu) def_list';
	    let def_vars' = !accu in
	    let above_node' = { above_node = above_node; binders = vars; 
				true_facts_at_def = true_facts'; 
				def_vars_at_def = def_vars';
				elsefind_facts_at_def = elsefind_facts;
				future_binders = []; future_true_facts = []; 
				definition = DProcess p';
			        definition_success = DProcess p1 } 
	    in
	    List.iter (fun b -> b.def <- above_node' :: b.def) vars;
	    ignore(def_term event_accu (def_term_def_list event_accu above_node true_facts def_vars def_list) true_facts def_vars_t t);
	    let (fut_binders1, fut_true_facts1) = 
	      def_oprocess event_accu above_node' true_facts' def_vars' elsefind_facts'' p1
	    in
	    above_node'.future_binders <- fut_binders1;
	    above_node'.future_true_facts <- fut_true_facts1;
	    (intersect (==) (vars @ fut_binders1) fut_bindersl,
	     intersect equal_terms fut_true_facts1 fut_true_factsl)
      in
      find_l l0
  | Output((c,tl),t',p) ->
      let above_node' = def_term_list event_accu above_node true_facts def_vars  tl in
      let above_node'' = def_term event_accu above_node' true_facts def_vars t' in
      def_process event_accu above_node'' true_facts def_vars p;
      ([],[])
  | Let(pat,t,p1,p2) ->
      let above_node' = def_term event_accu above_node true_facts def_vars t in
      let accu = ref [] in
      let above_node'' = def_pattern accu event_accu above_node' true_facts def_vars pat in
      let new_fact = (match pat with PatVar _ -> make_let_equal | _ -> make_equal) (term_from_pat pat) t in
      let true_facts' = new_fact :: true_facts in
      let vars_t_pat = def_vars_term (def_vars_pat [] pat) t in
      let elsefind_facts'' = List.filter (not_deflist_l vars_t_pat) elsefind_facts in
      let elsefind_facts' = List.filter (not_deflist_l (!accu)) elsefind_facts'' in
      let above_node''' = { above_node = above_node''; binders = !accu; 
			    true_facts_at_def = true_facts'; 
			    def_vars_at_def = def_vars;
			    elsefind_facts_at_def = elsefind_facts'';
			    future_binders = []; future_true_facts = []; 
			    definition = DProcess p';
			    definition_success = DProcess p1 } 
      in
      List.iter (fun b -> b.def <- above_node''' :: b.def) (!accu);
      let (fut_binders1, fut_true_facts1) = 
	def_oprocess event_accu above_node''' true_facts' def_vars elsefind_facts' p1
      in
      above_node'''.future_binders <- fut_binders1;
      above_node'''.future_true_facts <- fut_true_facts1;
      begin
	match pat, p2.p_desc with
	  PatVar _, Yield -> 
	    ((!accu) @ fut_binders1, new_fact :: fut_true_facts1)
	| _ -> 
	    let true_facts' = 
	      try
		(make_for_all_diff (gen_term_from_pat pat) t) :: true_facts
	      with NonLinearPattern -> true_facts
	    in
	    let (fut_binders2, fut_true_facts2) = 
	      def_oprocess event_accu above_node' true_facts' def_vars elsefind_facts'' p2
	    in
	    (intersect (==) ((!accu) @ fut_binders1) fut_binders2,
	     intersect equal_terms (new_fact :: fut_true_facts1) fut_true_facts2)
      end
  | EventP(t,p) ->
      begin
	match event_accu with
	  None -> ()
	| Some accu -> accu := (t, Some (true_facts, def_vars, above_node)) :: (!accu)
      end;
      let above_node' = def_term event_accu above_node true_facts def_vars t in
      let vars_t = def_vars_term [] t in
      let elsefind_facts' = List.filter (not_deflist_l vars_t) elsefind_facts in
      let (fut_binders, fut_true_facts) = 
	def_oprocess event_accu above_node' (t :: true_facts) def_vars elsefind_facts' p
      in
      (fut_binders, t::fut_true_facts)
  | Get(tbl,patl,topt,p1,p2) ->
      let accu = ref [] in
      let above_node' = def_pattern_list accu event_accu above_node true_facts def_vars patl in
      let above_node'' = 
        match topt with 
          Some t -> def_term event_accu above_node' true_facts def_vars t
        | None -> above_node'
      in
      (* The variables defined in patl, topt are variables defined in conditions of find,
	 one cannot make array accesses to them, nor test their definition,
	 so they will not appear in defined conditions of elsefind_facts.
	 We need not update elsefind_facts. *)
      let elsefind_facts' = List.filter (not_deflist_l (!accu)) elsefind_facts in
      let (fut_binders1, fut_true_facts1) = 
	def_oprocess event_accu above_node'' true_facts def_vars elsefind_facts' p1
      in
      let (fut_binders2, fut_true_facts2) = 
	def_oprocess event_accu above_node true_facts def_vars elsefind_facts p2
      in
      (intersect (==) fut_binders1 fut_binders2, 
       intersect equal_terms fut_true_facts1 fut_true_facts2)
        
  | Insert(tbl,tl,p) ->
      let vars_tl = def_vars_term_list [] tl in
      let elsefind_facts' = List.filter (not_deflist_l vars_tl) elsefind_facts in
      let above_node' = def_term_list event_accu above_node true_facts def_vars tl in
      def_oprocess event_accu above_node' true_facts def_vars elsefind_facts' p

let build_def_process event_accu p =
  empty_def_process p;
  let rec st_node = { above_node = st_node; 
		      binders = []; 
		      true_facts_at_def = []; 
		      def_vars_at_def = []; 
		      elsefind_facts_at_def = [];
		      future_binders = []; future_true_facts = []; 
		      definition = DNone;
		      definition_success = DNone } 
  in
  def_process event_accu st_node [] [] p

(* Add to [accu] the variables defined above the node [n] *)

let rec add_def_vars_node accu n =
  let accu' = n.binders @ accu in
  if n.above_node != n then
    add_def_vars_node accu' n.above_node
  else
    accu'


(* array_ref_* stores in the binders the kind of accesses made to the binder:
    - b.count_def: number of definitions of the binder b
    - b.std_ref: true when b has standard references (references to b 
      in its scope with the array indices at its definition)
    - b.array_ref: true when b has array references (references to b
      outside its scope or with explicit array indices that use the value of b)
    - b.root_def_std_ref: true when b is referenced at the root of a "defined"
      condition, in its scope with the array indices at its definition.
    - b.root_def_array_ref: true when b is referenced at the root of a "defined"
      condition, in an array reference. 
      If references at the root of defined conditions are the only ones, 
      the definition point of b is important, but not its value.

   It also stores the binders in all_vars, so that cleanup_array_ref
   can cleanup the binders; cleanup_array_ref should be called when
   the reference information is no longer needed.

   The treatment of TestE/FindE/LetE/ResE is necessary: array_ref_eqside
   is called in check.ml.
*)

let all_vars = ref []

let add b =
  if not (List.memq b (!all_vars)) then
    all_vars := b :: (!all_vars)

let rec array_ref_term in_scope t = 
  match t.t_desc with
    Var(b, l) -> 
      if is_args_at_creation b l &&
	List.memq b in_scope then
	b.std_ref <- true
      else
	begin
	  b.array_ref <- true;
      	  b.count_array_ref <- b.count_array_ref + 1
	end;
      add b;
      List.iter (array_ref_term in_scope) l
  | ReplIndex i -> ()
  | FunApp(_,l) ->
      List.iter (array_ref_term in_scope)  l
  | TestE(t1,t2,t3) ->
      array_ref_term in_scope t1;
      array_ref_term in_scope t2;
      array_ref_term in_scope t3
  | LetE(pat, t1, t2, topt) ->
      array_ref_pattern in_scope pat;
      array_ref_term in_scope t1;
      array_ref_term (vars_from_pat in_scope pat) t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> array_ref_term in_scope t3
      end
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list, t1,t2) ->
	List.iter (fun (b,_) -> add b; b.count_def <- b.count_def + 1) bl;
	let in_scope' = (List.map fst bl) @ in_scope in
	array_ref_def_list in_scope def_list;
	array_ref_term in_scope t1;
	array_ref_term in_scope' t2) l0;
      array_ref_term in_scope t3
  | ResE(b,t) ->
      add b;
      b.count_def <- b.count_def + 1;
      array_ref_term (b::in_scope) t
  | EventAbortE _ -> ()

and array_ref_pattern in_scope = function
    PatVar b -> 
      add b;
      b.count_def <- b.count_def + 1
  | PatTuple (f,l) -> List.iter (array_ref_pattern in_scope) l
  | PatEqual t -> array_ref_term in_scope t

and array_ref_def_list in_scope' def_list =
  List.iter (fun (b,l) -> 
    List.iter (array_ref_term in_scope') l;
    if is_args_at_creation b l &&
      List.memq b in_scope' then
      b.root_def_std_ref <- true
    else
      begin
	b.root_def_array_ref <- true;
	b.count_array_ref <- b.count_array_ref + 1
      end;
    add b) def_list

let rec array_ref_process in_scope p =
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      array_ref_process in_scope p1;
      array_ref_process in_scope p2
  | Repl(b,p) ->
      array_ref_process in_scope p
  | Input((_,tl),pat,p) ->
      List.iter (array_ref_term in_scope) tl;      
      array_ref_pattern in_scope pat;
      array_ref_oprocess (vars_from_pat in_scope pat) p

and array_ref_oprocess in_scope p = 
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b,p) ->
      add b;
      b.count_def <- b.count_def + 1;
      array_ref_oprocess (b::in_scope) p
  | Test(t,p1,p2) ->
      array_ref_term in_scope t;      
      array_ref_oprocess in_scope p1;
      array_ref_oprocess in_scope p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list,t,p1) ->
	List.iter (fun (b,_) -> add b; b.count_def <- b.count_def + 1) bl;
	let in_scope' = (List.map fst bl) @ in_scope in
	array_ref_def_list in_scope def_list;
	array_ref_term in_scope t;      
	array_ref_oprocess in_scope' p1) l0;
      array_ref_oprocess in_scope p2
  | Output((_,tl),t2,p) ->
      List.iter (array_ref_term in_scope) tl;      
      array_ref_term in_scope t2;
      array_ref_process in_scope p
  | Let(pat, t, p1, p2) ->
      array_ref_pattern in_scope pat;
      array_ref_term in_scope t;      
      array_ref_oprocess (vars_from_pat in_scope pat) p1;
      array_ref_oprocess in_scope p2
  | EventP(t,p) ->
      array_ref_term in_scope t;      
      array_ref_oprocess in_scope p
  | Get(tbl,patl,topt,p1,p2) ->
      List.iter (array_ref_pattern in_scope) patl;
      let in_scope' = vars_from_pat_list in_scope patl in
      (match topt with 
         | Some t -> array_ref_term in_scope' t
         | None -> ());
      array_ref_oprocess in_scope' p1;
      array_ref_oprocess in_scope p2
  | Insert(tbl,tl,p) ->
      List.iter (array_ref_term in_scope) tl;
      array_ref_oprocess in_scope p


let rec array_ref_fungroup in_scope = function
    ReplRestr(repl, restr, funlist) ->
      List.iter (array_ref_fungroup ((List.map fst restr) @ in_scope)) funlist
  | Fun(ch, args, res, priority) ->
      array_ref_term (args @ in_scope) res
      
let cleanup_array_ref() =
  List.iter (fun b ->
    b.count_def <- 0;
    b.root_def_array_ref <- false;
    b.root_def_std_ref <- false;
    b.array_ref <- false;
    b.std_ref <- false;
    b.count_array_ref <- 0;
    b.count_exclude_array_ref <- 0) (!all_vars);
  all_vars := []

let array_ref_process p =
  cleanup_array_ref();
  array_ref_process [] p

let array_ref_eqside rm =
  cleanup_array_ref();
  List.iter (fun (fg, _) -> array_ref_fungroup [] fg) rm

let has_array_ref b =
  b.root_def_array_ref || b.array_ref

let has_array_ref_q b =
  (has_array_ref b) || (Settings.occurs_in_queries b)

(* Functions that compute count_exclude_array_ref.
   The goal is to be able to easily determine if a variable has array
   references in the game outside a certain expression.
   One first computes array references in the full game, then
   one calls exclude_array_ref_term/exclude_array_ref_def_list on the
   part to exclude. 
   b has an array reference in the remaining part iff
   b.count_array_ref > b.count_exclude_array_ref *)

let all_vars_exclude = ref []

let add_exclude b =
  if not (List.memq b (!all_vars_exclude)) then
    all_vars_exclude := b :: (!all_vars_exclude)

let rec exclude_array_ref_term in_scope t = 
  match t.t_desc with
    Var(b, l) -> 
      if not (is_args_at_creation b l &&
	List.memq b in_scope) then
	begin
      	  b.count_exclude_array_ref <- b.count_exclude_array_ref + 1;
	  add_exclude b
	end;
      List.iter (exclude_array_ref_term in_scope) l
  | ReplIndex i -> ()
  | FunApp(_,l) ->
      List.iter (exclude_array_ref_term in_scope)  l
  | TestE(t1,t2,t3) ->
      exclude_array_ref_term in_scope t1;
      exclude_array_ref_term in_scope t2;
      exclude_array_ref_term in_scope t3
  | LetE(pat, t1, t2, topt) ->
      exclude_array_ref_pattern in_scope pat;
      exclude_array_ref_term in_scope t1;
      exclude_array_ref_term (vars_from_pat in_scope pat) t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> exclude_array_ref_term in_scope t3
      end
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	let in_scope' = (List.map fst bl) @ in_scope in
	exclude_array_ref_def_list in_scope def_list;
	exclude_array_ref_term in_scope t1;
	exclude_array_ref_term in_scope' t2) l0;
      exclude_array_ref_term in_scope t3
  | ResE(b,t) ->
      exclude_array_ref_term (b::in_scope) t
  | EventAbortE _ -> ()

and exclude_array_ref_pattern in_scope = function
    PatVar b -> ()
  | PatTuple (f,l) -> List.iter (exclude_array_ref_pattern in_scope) l
  | PatEqual t -> exclude_array_ref_term in_scope t

and exclude_array_ref_def_list in_scope' def_list = 
  List.iter (fun (b,l) -> 
    List.iter (exclude_array_ref_term in_scope') l;
    if not (is_args_at_creation b l &&
	    List.memq b in_scope') then
      begin
	b.count_exclude_array_ref <- b.count_exclude_array_ref + 1;
        add_exclude b
      end) def_list

let cleanup_exclude_array_ref() =
  List.iter (fun b ->
    b.count_exclude_array_ref <- 0) (!all_vars_exclude);
  all_vars_exclude := []

let has_array_ref_non_exclude b =
  b.count_array_ref > b.count_exclude_array_ref

(* Build the "incompatible" field for each program point [pp]. It
   contains the mapping of occurrences of program points [pp']
   incompatible with [pp] to the length [l] such that if [pp] with
   indices [arg] and [pp'] with indices [args'] are both executed,
   then the suffixes of length [l] of [args] and [args'] must be
   different.
   Supports LetE/FindE/ResE/TestE everywhere *)

(* Empty the "incompatible" field of all program points. *)

let rec empty_comp_pattern = function
    PatVar b -> ()
  | PatTuple (f,l) -> List.iter empty_comp_pattern l
  | PatEqual t -> empty_comp_term t

and empty_comp_term t =
  t.t_incompatible <- map_empty;
  match t.t_desc with
    Var (_,l) | FunApp(_,l)-> List.iter empty_comp_term l
  | ReplIndex _ -> ()
  | TestE(t1,t2,t3) -> 
      empty_comp_term t1;
      empty_comp_term t2;
      empty_comp_term t3
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	List.iter (fun (_,l) -> List.iter empty_comp_term l) def_list;
	empty_comp_term t1;
	empty_comp_term t2) l0;
      empty_comp_term t3
  | LetE(pat,t1,t2,topt) ->
      empty_comp_pattern pat;
      empty_comp_term t1;
      empty_comp_term t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> empty_comp_term t3
      end
  | ResE(b,p) ->
      empty_comp_term p
  | EventAbortE _ -> ()

let rec empty_comp_process p = 
  p.i_incompatible <- map_empty;
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      empty_comp_process p1;
      empty_comp_process p2
  | Repl(b,p) ->
      empty_comp_process p
  | Input((c,tl),pat,p) ->
      List.iter empty_comp_term tl;
      empty_comp_pattern pat;
      empty_comp_oprocess p

and empty_comp_oprocess p =
  p.p_incompatible <- map_empty;
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b,p) ->
      empty_comp_oprocess p
  | Test(t,p1,p2) ->
      empty_comp_term t;
      empty_comp_oprocess p1;
      empty_comp_oprocess p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list,t,p1) ->
	List.iter (fun (_,l) -> List.iter empty_comp_term l) def_list;
	empty_comp_term t;
	empty_comp_oprocess p1) l0;
      empty_comp_oprocess p2
  | Output((c,tl),t',p) ->
      List.iter empty_comp_term tl;
      empty_comp_term t';
      empty_comp_process p
  | Let(pat,t,p1,p2) ->
      empty_comp_pattern pat;
      empty_comp_term t;
      empty_comp_oprocess p1;
      empty_comp_oprocess p2
  | EventP(t,p) ->
      empty_comp_term t;
      empty_comp_oprocess p
  | Get(tbl,patl,topt,p1,p2) -> 
      List.iter empty_comp_pattern patl;
      begin
	match topt with
	  None -> ()
	| Some t -> empty_comp_term t
      end;
      empty_comp_oprocess p1;
      empty_comp_oprocess p2
  | Insert(tbl,tl,p) ->
      List.iter empty_comp_term tl;
      empty_comp_oprocess p

(* Compute the "incompatible" field for all program points *)

let rec compatible_def_term cur_array_length current_incompatible t = 
  t.t_incompatible <- current_incompatible;
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> 
      List.iter (compatible_def_term cur_array_length current_incompatible) l
  | ReplIndex i -> 
      ()
  | TestE(t1,t2,t3) -> 
      compatible_def_term cur_array_length current_incompatible t1;
      compatible_def_term cur_array_length current_incompatible t2;
      let t3_incompatible = Occ_map.add current_incompatible t2.t_occ t2.t_max_occ cur_array_length in
      compatible_def_term cur_array_length t3_incompatible t3 
  | FindE(l0, t3, _) ->
      let accu_incompatible = ref current_incompatible in
      List.iter (fun (bl, def_list, t1, t2) ->
	let cur_array_length_cond = cur_array_length + List.length bl in
	List.iter (fun (_,l) -> 
	  List.iter (compatible_def_term cur_array_length_cond current_incompatible) l) def_list;
	compatible_def_term cur_array_length_cond current_incompatible t1;
	compatible_def_term cur_array_length (!accu_incompatible) t2;
	accu_incompatible := (Occ_map.add (!accu_incompatible) t2.t_occ t2.t_max_occ cur_array_length)
	     ) l0;
      compatible_def_term cur_array_length (!accu_incompatible) t3
  | LetE(pat, t1, t2, topt) ->
      compatible_def_term cur_array_length current_incompatible t1;
      compatible_def_pat cur_array_length current_incompatible pat;
      compatible_def_term cur_array_length current_incompatible t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> 
	    let t3_incompatible = Occ_map.add current_incompatible t2.t_occ t2.t_max_occ cur_array_length in
	    compatible_def_term cur_array_length t3_incompatible t3 
      end
  | ResE(b,t2) ->
      compatible_def_term cur_array_length current_incompatible t2
  | EventAbortE _ ->
      ()

and compatible_def_pat cur_array_length current_incompatible = function
    PatVar b -> ()
  | PatTuple (f,l) -> List.iter (compatible_def_pat cur_array_length current_incompatible) l
  | PatEqual t -> compatible_def_term cur_array_length current_incompatible t

let rec compatible_def_process cur_array_length current_incompatible p =
  p.i_incompatible <- current_incompatible;
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) ->
      compatible_def_process cur_array_length current_incompatible p1;
      compatible_def_process cur_array_length current_incompatible p2
  | Repl(b,p) ->
      compatible_def_process (cur_array_length+1) current_incompatible p
  | Input((c,tl),pat,p2) ->
      List.iter (compatible_def_term cur_array_length current_incompatible) tl;
      compatible_def_pat cur_array_length current_incompatible pat;
      compatible_def_oprocess cur_array_length current_incompatible p2 

and compatible_def_oprocess cur_array_length current_incompatible p =
  p.p_incompatible <- current_incompatible;
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b, p2) ->
      compatible_def_oprocess cur_array_length current_incompatible p2 
  | Test(t,p1,p2) ->
      compatible_def_term cur_array_length current_incompatible t;
      compatible_def_oprocess cur_array_length current_incompatible p1;
      let p2_incompatible = Occ_map.add current_incompatible p1.p_occ p1.p_max_occ cur_array_length in
      compatible_def_oprocess cur_array_length p2_incompatible p2 
  | Find(l0, p2, _) ->
      let accu_incompatible = ref current_incompatible in
      List.iter (fun (bl, def_list, t, p1) ->
	let cur_array_length_cond = cur_array_length + List.length bl in
	List.iter (fun (_,l) -> 
	  List.iter (compatible_def_term cur_array_length_cond current_incompatible) l) def_list;
	compatible_def_term cur_array_length_cond current_incompatible t;
	compatible_def_oprocess cur_array_length (!accu_incompatible) p1;
	accu_incompatible := (Occ_map.add (!accu_incompatible) p1.p_occ p1.p_max_occ cur_array_length)
	     ) l0;
      compatible_def_oprocess cur_array_length (!accu_incompatible) p2
  | Output((c,tl),t2,p) ->
      List.iter (compatible_def_term cur_array_length current_incompatible) tl;
      compatible_def_term cur_array_length current_incompatible t2;
      compatible_def_process cur_array_length current_incompatible p
  | Let(pat,t,p1,p2) ->
      compatible_def_term cur_array_length current_incompatible t;
      compatible_def_pat cur_array_length current_incompatible pat;
      compatible_def_oprocess cur_array_length current_incompatible p1;
      let p2_incompatible = Occ_map.add current_incompatible p1.p_occ p1.p_max_occ cur_array_length in
      compatible_def_oprocess cur_array_length p2_incompatible p2 
  | EventP(t,p) ->
      compatible_def_term cur_array_length current_incompatible t;
      compatible_def_oprocess cur_array_length current_incompatible p
  | Get(_,_,_,_,_) | Insert (_,_,_) -> 
      internal_error "Get/Insert should have been reduced at this point"


let build_compatible_defs p = 
  compatible_def_process 0 map_empty p

(* [occ_from_pp pp] returns a triple containing
   - the occurrence of program point [pp]
   - the maximum occurrence of program points under [pp] in the syntax tree.
   (the occurrences of program points under [pp] are then
   in the interval [occurrence of [pp], max. occ. under [pp]])
   - the mapping of occurrences of program points [pp'] incompatible with [pp]
   to the length [l] such that if [pp] with indices [arg]
   and [pp'] with indices [args'] are both executed, then
   the suffixes of length [l] of [args] and [args'] must be different.
   Raises [Not_found] when [pp] does not uniquely identify a program point. *) 

let occ_from_pp = function
    DProcess(p) -> p.p_occ, p.p_max_occ, p.p_incompatible
  | DTerm(t) -> t.t_occ, t.t_max_occ, t.t_incompatible
  | DInputProcess(p) -> p.i_occ, p.i_max_occ, p.i_incompatible
  | _ -> raise Not_found

(* [map_max f l], where [f] is a function from list elements to integers,
   returns the maximum of [f a] for elements [a] in [l] *)

let rec map_max f = function
    [] -> 0
  | a::l -> max (f a) (map_max f l)

(* [incompatible_suffix_length_pp pp pp'] returns a length [l] such
   that if [pp] with indices [args] and [pp'] with indices [args'] are
   both executed, then the suffixes of length [l] of [args] and
   [args'] must be different.
   Raises [Not_found] when [pp] with indices [args] and [pp'] with
   indices [args'] can be executed for any [args,args'].*)

let incompatible_suffix_length_pp pp pp' =
  let occ, _, occ_map = occ_from_pp pp in
  let occ', _, occ_map' = occ_from_pp pp' in
  try 
    Occ_map.find occ occ_map' 
  with Not_found ->
    Occ_map.find occ' occ_map 

(* [both_pp_add_fact fact_accu (args, pp) (args', pp')] 
   adds to [fact_accu] a fact inferred from the execution of both
   program point [pp] with indices [args] and 
   program point [pp'] with indices [args'], if any.*)
	
let both_pp_add_fact fact_accu (args, pp) (args', pp') =
  try
    let suffix_l = incompatible_suffix_length_pp pp pp' in
    let args_skip = lsuffix suffix_l args in
    let args_skip' = lsuffix suffix_l args' in
    fact_accu := (make_or_list (List.map2 make_diff args_skip args_skip')) :: (!fact_accu)    
  with Not_found -> ()

(* [incompatible_suffix_length_onepp pp b'] returns a length [l] such
   that if [pp] with indices [args] is executed and [b'[args]] 
   is defined, then the suffixes of length [l] of [args] and
   [args'] must be different.
   Raises [Not_found] when [pp] with indices [args] can be executed 
   and [b'[args']] can be defined for any [args,args'].*)

let incompatible_suffix_length_onepp pp b' =
  let pp_occ, _, pp_occ_map = occ_from_pp pp in
  map_max (fun n' ->
    let (occ', _, occ_map') = occ_from_pp n'.definition_success in
    try 
      Occ_map.find pp_occ occ_map' 
    with Not_found ->
      Occ_map.find occ' pp_occ_map 
	) b'.def

(* [incompatible_suffix_length b b'] returns a length [l] such that if
   [b[args]] and [b'[args']] are both defined, then the suffixes of
   length [l] of [args] and [args'] must be different.
   Raises [Not_found] when [b[args]] and [b'[args']] can be defined 
   for any [args,args']. *)

let incompatible_suffix_length b b' =
  map_max (fun n -> incompatible_suffix_length_onepp n.definition_success b') b.def

(* [is_compatible (b,args) (b',args')] returns true when
   [b[args]] and [b'[args']] may both be defined *)

let is_compatible (b,args) (b',args') =
  (b == b') || 
  (try
    let suffix_l = incompatible_suffix_length b b' in
    let args_skip = lsuffix suffix_l args in
    let args_skip' = lsuffix suffix_l args' in
    (not (List.for_all2 equal_terms args_skip args_skip'))
  with Not_found -> true)

(* [is_compatible_node (b,args) n (b',args')] returns true when
   [b[args]] and [b'[args']] may both be defined, with [b[args]]
   defined at node [n]. *)

let is_compatible_node (b,args) n (b',args') =
  (b == b') || 
  (try
    let suffix_l = incompatible_suffix_length_onepp n.definition_success b' in
    (*print_string ("incompatible_suffix_length 1 " ^ b.sname ^ "_" ^ (string_of_int b.vname) ^ " " ^ b'.sname ^ "_" ^ (string_of_int b'.vname) ^ " = "); print_int suffix_l; print_newline(); *)
    let args_skip = lsuffix suffix_l args in
    let args_skip' = lsuffix suffix_l args' in
    (not (List.for_all2 equal_terms args_skip args_skip'))
  with Not_found -> true)

(* [both_def_add_fact fact_accu (b,args) (b',args')]
   adds to [fact_accu] a fact that always holds when
   [b[args]] and [b'[args']] are both defined, if any. *)

let both_def_add_fact fact_accu (b,args) (b',args') =
  if b != b' then 
    try
      let suffix_l = incompatible_suffix_length b b' in
      let args_skip = lsuffix suffix_l args in
      let args_skip' = lsuffix suffix_l args' in
      fact_accu := (make_or_list (List.map2 make_diff args_skip args_skip')) :: (!fact_accu)    
    with Not_found -> ()

(* [not_after_suffix_length_one_pp pp length_cur_array_pp b'] returns
   the shortest length [l] such that the program point [pp] cannot be
   executed with indices [args] after the definition of variable [b']
   with indices [args'] when [args] and [args'] have a common suffix of
   length [l].  
   Raises [Not_found] when [pp] with indices [args] can be executed
   after the definition of [b'[args']] for any [args,args'].
   [length_cur_array_pp] is the number of replication indices at
   program point [pp]. *)

let not_after_suffix_length_one_pp pp length_cur_array_pp b' =
  let pp_occ, pp_max_occ, pp_occ_map = occ_from_pp pp in
  map_max (fun n' ->
    let (occ', _, occ_map') = occ_from_pp n'.definition_success in
    try 
      Occ_map.find pp_occ occ_map' 
    with Not_found ->
      try
	Occ_map.find occ' pp_occ_map
      with Not_found ->
	if pp_occ <= occ' && occ' <= pp_max_occ then
	  length_cur_array_pp (* since b' is defined under pp, b' has more indices than pp *)
	else
	  raise Not_found
	) b'.def


(* [def_at_pp_add_fact fact_accu pp args (b',args')] adds to
   [fact_accu] a fact that always holds when [b'[args']] is defined
   before the execution of program point [pp] with indices [args], if
   any. *)

let def_at_pp_add_fact fact_accu pp args (b',args') =
  let length_cur_array_pp = List.length args in
  try
    let suffix_l = not_after_suffix_length_one_pp pp length_cur_array_pp b' in
    let args_skip = lsuffix suffix_l args in
    let args_skip' = lsuffix suffix_l args' in
    fact_accu := (make_or_list (List.map2 make_diff args_skip args_skip')) :: (!fact_accu)    
  with Not_found -> ()
    
(* [may_def_before (b,args) (b',args')] returns true when
   [b[args]] may be defined before [b'[args']] *)

let may_def_before (b,args) (b',args') = 
  (b == b') || 
  (try
    let length_cur_array_b' = List.length args' in
    let suffix_l = map_max (fun n -> not_after_suffix_length_one_pp n.definition_success length_cur_array_b' b) b'.def in
    let args_skip = lsuffix suffix_l args in
    let args_skip' = lsuffix suffix_l args' in
    (not (List.for_all2 equal_terms args_skip args_skip'))
  with Not_found -> true)

(* Update args_at_creation: since variables in conditions of find have
as args_at_creation the indices of the find, transformations of the
find may lead to changes in these indices.  This function updates
these indices. It relies on the invariant that variables in conditions
of find have no array accesses, and that new/event do not occur in
conditions of find. It creates fresh variables for all variables
defined in the condition of the find. *)

let rec update_args_at_creation cur_array t =
  match t.t_desc with
    Var(b,l) ->
      begin
      match b.link with
	NoLink -> build_term2 t (Var(b, List.map (update_args_at_creation cur_array) l))
      |	TLink t' -> 
	  (* Variable b is defined in the current find condition, 
             it has no array accesses *)
	  t'
      end
  | ReplIndex b -> t
  | FunApp(f,l) -> build_term2 t (FunApp(f, List.map (update_args_at_creation cur_array) l))
  | ResE _ | EventAbortE _ ->
      Parsing_helper.internal_error "new/event should not occur as term in find condition" 
  | TestE(t1,t2,t3) ->
       build_term2 t (TestE(update_args_at_creation cur_array t1,
			    update_args_at_creation cur_array t2,
			    update_args_at_creation cur_array t3))
  | FindE(l0,t3,find_info) ->
      let l0' = 
	List.map (fun (bl, def_list, t1, t2) ->
	  let repl_indices = List.map snd bl in
	  let cur_array_cond = repl_indices @ cur_array in
	  let def_list' = List.map (update_args_at_creation_br cur_array_cond) def_list in
	  let t1' = update_args_at_creation cur_array_cond t1 in
	  let bl' = List.map (fun (b,b') ->
	    let b1 = create_binder b.sname (new_vname()) b.btype cur_array in
	    link b (TLink (term_from_binder b1));
	    (b1, b')) bl 
	  in
	  let t2' = update_args_at_creation cur_array t2 in
	  (bl', def_list', t1', t2')
	  ) l0
      in
      build_term2 t (FindE(l0',
				 update_args_at_creation cur_array t3,
				 find_info))
  | LetE(pat, t1, t2, topt) ->
      let t1' = update_args_at_creation cur_array t1 in
      let pat' = update_args_at_creation_pat cur_array pat in
      let t2' = update_args_at_creation cur_array t2 in
      let topt' = 
	match topt with
	  None -> None
	| Some t3 -> Some (update_args_at_creation cur_array t3)
      in
      build_term2 t (LetE(pat', t1', t2', topt'))

and update_args_at_creation_br cur_array (b,l) =
  begin
    match b.link with
      NoLink -> (b, List.map (update_args_at_creation cur_array) l)
    | TLink t' -> 
        (* Variable b is defined in the current find condition, 
           it has no array accesses *)
	binderref_from_term t'
  end

and update_args_at_creation_pat cur_array = function
    PatVar b ->
      let b' = create_binder b.sname (new_vname()) b.btype cur_array in
      link b (TLink (term_from_binder b'));
      PatVar b'
  | PatTuple(f,l) ->
      PatTuple(f, List.map (update_args_at_creation_pat cur_array) l)
  | PatEqual t ->
      PatEqual (update_args_at_creation cur_array t)
      

let update_args_at_creation cur_array t =
  auto_cleanup (fun () ->
    update_args_at_creation cur_array t)

(* get needed def_list elements *)

let rec get_needed_deflist_term defined accu t =
  match t.t_desc with
    Var(b,l) -> 
      let br = (b,l) in
      if not (mem_binderref br defined) then
	add_binderref br accu
  | ReplIndex i -> ()
  | FunApp(f,l) -> List.iter (get_needed_deflist_term defined accu) l
  | TestE(t1,t2,t3) -> 
      get_needed_deflist_term defined accu t1;
      get_needed_deflist_term defined accu t2;
      get_needed_deflist_term defined accu t3
  | FindE(l0,t3, find_info) ->
      List.iter (fun (bl, def_list, t, t1) ->
	let (defined_t, defined_t1) = defined_refs_find bl def_list defined in
	get_needed_deflist_term defined_t accu t;
	get_needed_deflist_term defined_t1 accu t1
	) l0;
      get_needed_deflist_term defined accu t3
  | LetE(pat,t1,t2,topt) ->
      get_needed_deflist_pat defined accu pat;
      get_needed_deflist_term defined accu t1;
      let bpat = vars_from_pat [] pat in
      let defs = List.map binderref_from_binder bpat in
      get_needed_deflist_term (defs @ defined) accu t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> get_needed_deflist_term defined accu t3
      end
  | ResE(b,t) -> get_needed_deflist_term ((binderref_from_binder b)::defined) accu t
  | EventAbortE f -> ()

and get_needed_deflist_pat defined accu = function
    PatVar _ -> ()
  | PatTuple(f,l) -> List.iter (get_needed_deflist_pat defined accu) l
  | PatEqual t -> get_needed_deflist_term defined accu t

let rec get_needed_deflist_process defined accu p = 
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> get_needed_deflist_process defined accu p1;
      get_needed_deflist_process defined accu p2
  | Repl(b,p) -> get_needed_deflist_process defined accu p
  | Input((c,tl),pat,p) ->
      List.iter (get_needed_deflist_term defined accu) tl;
      get_needed_deflist_pat defined accu pat;
      let bpat = vars_from_pat [] pat in
      let defs = List.map binderref_from_binder bpat in
      get_needed_deflist_oprocess (defs @ defined) accu p

and get_needed_deflist_oprocess defined accu p =
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b,p) -> get_needed_deflist_oprocess ((binderref_from_binder b)::defined) accu p
  | Test(t,p1,p2) -> 
      get_needed_deflist_term defined accu t;
      get_needed_deflist_oprocess defined accu p1;
      get_needed_deflist_oprocess defined accu p2
  | Find(l0,p2, find_info) ->
      List.iter (fun (bl, def_list, t, p1) ->
	let (defined_t, defined_p1) = defined_refs_find bl def_list defined in
	get_needed_deflist_term defined_t accu t;
	get_needed_deflist_oprocess defined_p1 accu p1
	) l0;
      get_needed_deflist_oprocess defined accu p2
  | Let(pat,t,p1,p2) ->
      get_needed_deflist_pat defined accu pat;
      get_needed_deflist_term defined accu t;
      let bpat = vars_from_pat [] pat in
      let defs = List.map binderref_from_binder bpat in
      get_needed_deflist_oprocess (defs @ defined) accu p1;
      get_needed_deflist_oprocess defined accu p2
  | Output((c,tl),t2,p) ->
      List.iter (get_needed_deflist_term defined accu) tl;
      get_needed_deflist_term defined accu t2;
      get_needed_deflist_process defined accu p
  | EventP(t,p) ->
      get_needed_deflist_term defined accu t;
      get_needed_deflist_oprocess defined accu p
  | Get(tbl,patl,topt,p1,p2) ->
      List.iter (get_needed_deflist_pat defined accu) patl;
      let bpat = List.fold_left vars_from_pat [] patl in
      let defs = (List.map binderref_from_binder bpat) @ defined in
      (match topt with None -> () | Some t -> get_needed_deflist_term defs accu t);
      get_needed_deflist_oprocess defs accu p1;
      get_needed_deflist_oprocess defined accu p2
  | Insert(tbl,tl,p) ->
      List.iter (get_needed_deflist_term defined accu) tl;
      get_needed_deflist_oprocess defined accu p

(********** Use the equational theory to simplify a term *************)

(* Remark: applying remove_consecutive_inverse and remove_inverse_ends
to t1 * inv(t2) does the same job as applying 
- remove_consecutive_inverse to t1 and to t2, 
- remove_common_prefix and remove_common_suffix to the obtained t1 t2, 
- and remove_inverse_ends to t1 in case t2 is the neutral element and conversely.
We do the latter below. (One advantage is that the form of the simplified
term is then closer to the initial term.) *)

let rec remove_common_prefix simp_facts reduced l1 l2 = 
  match (l1,l2) with
    t1::r1, t2::r2 when simp_equal_terms simp_facts true t1 t2 -> 
      reduced := true;
      remove_common_prefix simp_facts reduced r1 r2
  | _ -> (l1,l2)
      
let remove_common_suffix simp_facts reduced l1 l2 = 
  let l1rev = List.rev l1 in
  let l2rev = List.rev l2 in
  let (l1rev',l2rev') = remove_common_prefix simp_facts reduced l1rev l2rev in
  (List.rev l1rev', List.rev l2rev')

let is_fun f t =
  match t.t_desc with
    FunApp(f',_) -> f == f' 
  | _ -> false

(* collect_first_inverses inv [] [inv(t1); ... inv(tn); rest] 
   is ([tn; ...; t1], rest) *)

let rec collect_first_inverses inv accu = function
    [] -> (accu, [])
  | (t::l) ->
      match t.t_desc with
	FunApp(f,[tinv]) when f == inv -> 
	  collect_first_inverses inv (tinv::accu) l
      |	_ -> (accu, t::l)

(* when l = inv(t1) * ... * inv(tn) * rest' * inv(t'_n') * ... * inv(t'_1),
   collect_first_and_last_inverses is
   (l1',l2') = (tn * ... * t1 * l1 * t'_1 * ... * t'_n', rest)
   so that l = l1 is equivalent to l1' = l2'.
   (Lists represent products.) *)

let collect_first_and_last_inverses reduced inv l1 l =
  let (first_inv, rest) = collect_first_inverses inv [] l in
  (* first_inv = tn * ... * t1, rest = rest' * inv(t'_n') * ... * inv(t'_1) *)
  let rest_rev = List.rev rest in
  (* rest_rev = inv(t'_1) * ... * inv(t'_n') * List.rev rest' *)
  let (last_inv_rev, rest_rev') = collect_first_inverses inv [] rest_rev in
  (* last_inv_rev = t'_n' * ... * t'_1, rest_rev' = List.rev rest' *)
  if first_inv != [] || last_inv_rev != [] then reduced := true;
  (first_inv @ l1 @ (List.rev last_inv_rev), List.rev rest_rev')

(* apply_eq_reds implements reduction rules coming from the
   equational theories, as well as
     not (x = y) -> x != y
     not (x != y) -> x = y
     x = x -> true
     x != x -> false
     ?x != t -> false where ?x is a general variable (universally quantified)
(These rules cannot be stored in file default, because there are several
functions for = and for !=, one for each type.)
*)

let rec apply_eq_reds simp_facts reduced t =
  match t.t_desc with
(* not (x = y) -> x != y
   not (x != y) -> x = y *)
    FunApp(fnot, [t']) when fnot == Settings.f_not ->
      begin
      let t' = try_no_var simp_facts t' in
      match t'.t_desc with
	FunApp(feq, [t1;t2]) when feq.f_cat == Equal ->
	  reduced := true;
	  apply_eq_reds simp_facts reduced (make_diff t1 t2)
      |	FunApp(fdiff, [t1;t2]) when fdiff.f_cat == Diff ->
	  reduced := true;
	  apply_eq_reds simp_facts reduced (make_equal t1 t2)
      |	_ -> make_not (apply_eq_reds simp_facts reduced t')
      end

(* simplify inv(M): inv(neut) -> neut; inv(inv(M)) -> M; inv(M * M') -> inv(M') * inv(M) *)
  | FunApp({f_eq_theories = (Group(f,inv',n) | CommutGroup(f,inv',n)) } as inv, [t']) when inv' == inv ->
      (* inv is an inverse function *)
      let t' = apply_eq_reds simp_facts reduced t' in
      compute_inv (try_no_var simp_facts) reduced (f,inv',n) t'

(* Simplify and/or when one side is known to be true/false
   It is important that this case is tested before the more general case below. *)
  | FunApp(f,[t1;t2]) when f == Settings.f_and ->
      let t1' = apply_eq_reds simp_facts reduced t1 in
      let t2' = apply_eq_reds simp_facts reduced t2 in
      if (is_true t1') || (is_false t2') then
	begin
	  reduced := true; t2'
	end
      else if (is_true t2') || (is_false t1') then
	begin
	  reduced := true; t1'
	end
      else
	build_term2 t (FunApp(f, [t1';t2']))
  | FunApp(f,[t1;t2]) when f == Settings.f_or ->
      let t1' = apply_eq_reds simp_facts reduced t1 in
      let t2' = apply_eq_reds simp_facts reduced t2 in
      if (is_false t1') || (is_true t2') then
	begin
	  reduced := true; t2'
	end
      else if (is_false t2') || (is_true t1') then
	begin
	  reduced := true; t1'
	end
      else
	build_term2 t (FunApp(f, [t1';t2']))

(* simplify products: eliminate factors that cancel out *)
  | FunApp(f,[t1;t2]) when f.f_eq_theories != NoEq && f.f_eq_theories != Commut &&
    f.f_eq_theories != Assoc && f.f_eq_theories != AssocCommut ->
      (* f is a binary function with an equational theory that is
	 not commutativity nor inverse -> it is a product-like function *)
      begin
	match f.f_eq_theories with
	  NoEq | Commut | Assoc | AssocCommut -> 
	    Parsing_helper.internal_error "Terms.apply_eq_reds: cases NoEq, Commut, Assoc, AssocCommut should have been eliminated"
	| AssocN(_, neut) | AssocCommutN(_, neut) -> 
	    (* eliminate the neutral element *)
	    if is_fun neut t1 then 
	      begin
		reduced := true;
		apply_eq_reds simp_facts reduced t2
	      end
	    else if is_fun neut t2 then
	      begin
		reduced := true;
		apply_eq_reds simp_facts reduced t1
	      end
	    else
	      build_term2 t (FunApp(f, [ apply_eq_reds simp_facts reduced t1;
					 apply_eq_reds simp_facts reduced t2 ]))	      
	| Group _ | CommutGroup _ | ACUN _ ->
	    (* eliminate factors that cancel out and the neutral element *)
	    let reduced' = ref false in
	    let l1 = simp_prod simp_facts reduced' f t in
	    if !reduced' then
	      begin
		reduced := true;
		let l1 = List.map (apply_eq_reds simp_facts reduced) l1 in
		make_prod f l1
	      end
	    else
	      build_term2 t (FunApp(f, [ apply_eq_reds simp_facts reduced t1;
					 apply_eq_reds simp_facts reduced t2 ]))
      end

(* simplify equalities and inequalities:
     x = x -> true
     x != x -> false
as well as equalities between products *)
  | FunApp(f, [t1;t2]) when (f.f_cat == Equal || f.f_cat == Diff) ->
      begin
	if simp_equal_terms simp_facts true t1 t2 then
	  begin
	    reduced := true;
	    match f.f_cat with
	      Equal -> make_true()
	    | Diff -> make_false()
	    | _ -> assert false
	  end
	else
	match get_prod_list (try_no_var simp_facts) [t1;t2] with
	  ACUN(xor,neut) ->
	    let reduced' = ref false in
	    let l1 = simp_prod simp_facts reduced' xor (app xor [t1;t2]) in
	    if !reduced' then
	      begin
		reduced := true;
		let l1 = List.map (apply_eq_reds simp_facts reduced) l1 in
		match l1 with
		  [] -> 
		    begin
		      match f.f_cat with
			Equal -> make_true()
		      | Diff -> make_false()
		      | _ -> assert false
		    end
		| t1::l -> build_term2 t (FunApp(f,[t1;make_prod xor l]))
		      (* The number of terms that appear here is always strictly
			 less than the initial number of terms:
			 the number of terms in l1 is strictly less than the number of terms
			 in t1 plus t2; make_prod introduces an additional neutral
			 term when l = []; in this case, we have two terms 
			 in the final result, and at least 3 in the initial t1 = t2,
			 since the side that contains the XOR symbol returned by get_prod_list
			 contains at least two terms. 
			 Hence, we always really simplify the term. *)
	      end
	    else
	      build_term2 t (FunApp(f, [ apply_eq_reds simp_facts reduced t1;
					 apply_eq_reds simp_facts reduced t2 ]))
	| CommutGroup(prod,inv,neut) ->
	    let reduced' = ref false in
	    let lmix =
	      if is_fun neut t1 then
		let l2 = simp_main_fun (try_no_var simp_facts) reduced' prod t2 in
		reduced' := (!reduced') || (List.exists (is_fun inv) l2);
		l2
	      else if is_fun neut t2 then
		let l1 = simp_main_fun (try_no_var simp_facts) reduced' prod t1 in
		reduced' := (!reduced') || (List.exists (is_fun inv) l1);
		l1
	      else
		let l1 = simp_main_fun (try_no_var simp_facts) reduced' prod t1 in
		let l2 = simp_main_fun (try_no_var simp_facts) reduced' prod t2 in
		reduced' := (!reduced') || (List.exists (is_fun inv) l1) ||
		  (List.exists (is_fun inv) l2);
		l1 @ (List.map (compute_inv (try_no_var simp_facts) reduced' (prod, inv, neut)) l2)
	        (* t2 = t1 is equivalent to t1 * t2^-1 = neut *)

	      (* It is important to treat the cases t1 or t2 neutral specially above.
		 Otherwise, we would leave M1 * M2 = neut unchanged, while still setting
		 reduced to true because simp_prod eliminates neut.

		 reduced' is set when t1 or t2 contains an inverse,
		 since this inverse will be removed by the final
		 building of the result below. *)
	    in
	    let l1 = remove_inverse simp_facts reduced' (prod,inv,neut) lmix in
	    if !reduced' then
	      begin
		reduced := true;
		let l1 = List.map (apply_eq_reds simp_facts reduced) l1 in
		match l1 with
		  [] -> 
		    begin
		      match f.f_cat with
			Equal -> make_true()
		      | Diff -> make_false()
		      | _ -> assert false
		    end
		| l -> 
		    let linv, lno_inv = List.partition (is_fun inv) l in
		    let linv_removed = List.map (function { t_desc = FunApp(f,[t]) } when f == inv -> t | _ -> assert false) linv in
		    build_term2 t (FunApp(f, [ make_prod prod lno_inv; 
					       make_prod prod linv_removed ]))
	      end
	    else
	      build_term2 t (FunApp(f, [ apply_eq_reds simp_facts reduced t1;
					 apply_eq_reds simp_facts reduced t2 ]))
	| Group(prod,inv,neut) ->
	    let reduced' = ref false in
	    let l1 = 
	      (* When t1 is the neutral element, applying simp_prod would
		 set reduced' to true, so one would iterate simplification.
		 However, the neutral element will be reintroduced by
		 make_prod below, so that could lead to a loop. 
		 We detect this special case, and avoid setting reduced'
		 in this case. *)
	      if is_fun neut t1 then [] else
	      simp_prod simp_facts reduced' prod t1 
	    in
	    let l2 = 
	      if is_fun neut t2 then [] else
	      simp_prod simp_facts reduced' prod t2 
	    in
	    let (l1',l2') = remove_common_prefix simp_facts reduced' l1 l2 in
	    let (l1'',l2'') = remove_common_suffix simp_facts reduced' l1' l2' in
	    let l1'' = if l2'' == [] then remove_inverse_ends simp_facts reduced' (prod, inv, neut) l1'' else l1'' in
	    let l2'' = if l1'' == [] then remove_inverse_ends simp_facts reduced' (prod, inv, neut) l2'' else l2'' in
	    let (l1'', l2'') = collect_first_and_last_inverses reduced' inv l1'' l2'' in
	    let (l1'', l2'') = collect_first_and_last_inverses reduced' inv l2'' l1'' in
	    if !reduced' then
	      begin
		reduced := true;
		let l1 = List.map (apply_eq_reds simp_facts reduced) l1'' in
		let l2 = List.map (apply_eq_reds simp_facts reduced) l2'' in
		match l1,l2 with
		  [],[] -> 
		    begin
		      match f.f_cat with
			Equal -> make_true()
		      | Diff -> make_false()
		      | _ -> assert false
		    end
		| _ -> 
		    build_term2 t (FunApp(f, [ make_prod prod l1; 
					       make_prod prod l2 ]))
	      end
	    else
	      build_term2 t (FunApp(f, [ apply_eq_reds simp_facts reduced t1;
					 apply_eq_reds simp_facts reduced t2 ]))
	| _ -> 
	    build_term2 t (FunApp(f, [ apply_eq_reds simp_facts reduced t1;
				       apply_eq_reds simp_facts reduced t2 ]))
      end

(* ?x <> t is always false when ?x is a general variable (universally quantified) *)
  | FunApp(f,[{t_desc = Var(b,[])};t2]) when f.f_cat == ForAllDiff && 
    b.sname == gvar_name && not (refers_to b t2) -> 
      reduced := true;
      make_false()      
  | FunApp(f,[t2;{t_desc = Var(b,[])}]) when f.f_cat == ForAllDiff && 
    b.sname == gvar_name && not (refers_to b t2) -> 
      reduced := true;
      make_false()      

(* Simplify subterms *)
  | FunApp(f,l) ->
      build_term2 t (FunApp(f, List.map (apply_eq_reds simp_facts reduced) l))
  | _ -> t


(*********** Matching modulo equational theory *************)

(* Common arguments for the matching functions:

   [match_term]: [match_term next_f t1 t2 state] matches [t1] with [t2];
   calls [next_f state'] when the match succeeds; raises NoMatch when it
   fails. It must clean up the links it has put at least when it fails.
   (When it succeeds, the cleanup is optional.)

   [get_var_link]: [get_var_link t state] returns [Some (link, allow_neut)]
   when [t] is variable that can be bound by a product of terms,
   [link] is the current contents of the link of that variable,
   [allow_neut] is true if and only if the variable may be bound to
   the neutral element (provided there is a neutral element for the
   product); it returns [None] otherwise.

   [match_error]: [match_error()] is called in case of matching error.
   (In most cases, [match_error] should be [default_match_error]
   which raises the [NoMatch] exception.)

   [simp_facts] collects the rewrite rules corresponding to known equalities
   and other known facts, which we use in order to replace variables with their values and
   to test equality between terms.

   [prod] is the product function symbol, which is associative or AC.

   [allow_rest] is true when we match inside a subterm, so that some
   elements of the products are allowed to remain unmatched.
   *)


let default_match_error() = raise NoMatch

(* [prod_has_neut prod] returns true if and only if the product
   [prod] has a neutral element. *)

let prod_has_neut prod =
  (* Look for the neutral element of the product *)
  match prod.f_eq_theories with
    Group(_,_,n) | CommutGroup(_,_,n) | AssocN(_,n) 
  | AssocCommutN(_,n) | ACUN(_,n) -> true
  | _ -> false

(* Matching modulo associativity, plus perhaps neutral element *)

(* [remove_list_prefix simp_facts l1 l2] checks that [l1] is equal to a prefix of [l2],
   and returns the remaining suffix of [l2] after removing [l1]. *)

let rec remove_list_prefix simp_facts l1 l2 =
  match (l1,l2) with
    [], _ -> l2
  | _::_, [] -> raise Not_found
  | t1::r1, t2::r2 ->  
      if not (simp_equal_terms simp_facts true t1 t2) then raise Not_found;
      remove_list_prefix simp_facts r1 r2

let final_step match_error next_f allow_rest l2 state =
  if (l2 == []) || allow_rest then next_f l2 state else match_error()


(* [match_assoc match_term get_var_link match_error next_f simp_facts prod allow_rest l1 l2 state]
   matches the lists [l1] and [l2] modulo associativity. 
   When [allow_rest] is false, it calls [next_f [] state'] after linking variables in [l1]
   so that [\sigma l1 = l2] modulo associativity. 
   When [allow_rest] is true, it calls [next_f lrest state']  after linking variables in [l1]
   so that [\sigma l1 . lrest = l2] modulo associativity. *)

let match_assoc match_term get_var_link match_error next_f simp_facts prod allow_rest l1 l2 state =
  (* [has_neut] is true iff there is a neutral element for the product [prod]. *)
  let has_neut = prod_has_neut prod in
  if (not has_neut) && (List.length l1 > List.length l2) then match_error() else

  (* is_rev is true when the lists l1 and l2 have been reversed.
     In this case, when a variable is assigned or read, its content
     must also be reversed. *)
  let rec match_assoc_rec is_rev l1 l2 state =
    match l1 with
    | [] -> final_step match_error next_f allow_rest l2 state
    | t1::r1 ->
	match get_var_link t1 state, l2 with
	  None, [] -> match_error()
	| None, t2::r2 -> 
	    match_term (match_assoc_rec is_rev r1 r2) t1 t2 state
	| Some (TLink t, _), _ ->
            let l1' = simp_prod simp_facts (ref false) prod t in
	    let l1' = if is_rev then List.rev l1' else l1' in
	    begin
	      try 
		let r2 = remove_list_prefix simp_facts l1' l2 in
		match_assoc_rec is_rev r1 r2 state
	      with Not_found -> match_error()
	    end
	| Some (NoLink, allow_neut), _ ->
	    if (not allow_rest) && (r1 == []) then
	      begin
	        (* If variable v is alone, that's easy: v should be linked to l2 *)
		if (not (has_neut && allow_neut)) && (l2 == []) then match_error() else
		let t' = make_prod prod (if is_rev then List.rev l2 else l2) in
		match_term (next_f []) t1 t' state
	      end
	    else
	      begin
	        (* try to see if the end of the list contains something that is not an unbound variable *)
		let l1rev = List.rev l1 in
		if allow_rest || (match get_var_link (List.hd l1rev) state with
		                    Some (NoLink, _) -> true
		                  | _ -> false) then
		  (* l1 starts and ends with a variable, I really need to try all prefixes
		     of l2 as values for variable v. That can be costly.
		     I try the prefixes by first trying l2 entirely, then removing the
		     last element of l2, etc. until I try the empty list. 
		     The reason for this order is that, in case we match a subterm of the
		     product, we want to take the largest possible subterm that works. *)
		  let rec try_prefixes seen r2 =
		    try 
		      (* Try with at least one more element as seen if possible *)
		      match r2 with
			[] -> match_error()
		      | a::l -> 
			  if (not has_neut) && (List.length r1 > List.length l) then match_error() else
			  try_prefixes (seen @ [a]) l
		    with NoMatch ->
		      (* Try the list "seen" *)
		      if (seen == []) && (not (has_neut && allow_neut)) then match_error() else
		      match_term (match_assoc_rec is_rev r1 r2) t1 
			(make_prod prod (if is_rev then List.rev seen else seen)) state;
		  in
		  try_prefixes [] l2
		else
		  let l2rev = List.rev l2 in
		  match_assoc_rec (not is_rev) l1rev l2rev state
	      end
  in
  match_assoc_rec false l1 l2 state

(* [match_assoc_subterm match_term get_var_link next_f simp_facts prod l1 l2 state]
   matches the lists [l1] and [l2] modulo associativity. 
   More precisely, it calls [next_f left_rest right_rest]  after linking variables in [l1]
   so that [left_rest. \sigma l1 . right_rest = l2] modulo associativity. *)

let match_assoc_subterm match_term get_var_link next_f simp_facts prod l1 l2 state =
  let rec try_prefix seen l =
    try
      (* Try to match [l1] with [l], assuming [seen] will be the left rest of the subterm *)
      match_assoc match_term get_var_link default_match_error (fun right_rest -> next_f seen right_rest) simp_facts prod true l1 l state
    with NoMatch ->
      (* If it does not work, try with one more element in the left rest *)
      match l with
	[] -> raise NoMatch
      |	a::r -> 
	  try_prefix (seen @ [a]) r
  in
  try_prefix [] l2

(* Matching modulo associativity and commutativity, plus perhaps neutral element *)

(* [remove_elem simp_facts a l] returns list [l] after removing element [a] *)

let rec remove_elem simp_facts a = function
    [] -> raise Not_found
  | a'::l ->
      if simp_equal_terms simp_facts true a a' then l else
      a'::(remove_elem simp_facts a l)
	  
(* [multiset_minus simp_facts l lrem] returns list [l] after removing
   the elements in [lrem] *)

let rec multiset_minus simp_facts l = function
    [] -> l
  | a::r ->
      multiset_minus simp_facts (remove_elem simp_facts a l) r

let rec count_occ list_occ = function
    [] -> list_occ
  | (v::l) ->
      try
	let count = List.assq v list_occ in
	incr count;
	count_occ list_occ l
      with Not_found ->
	count_occ ((v, ref 1)::list_occ) l

let rec group_same_occ ((n, vl) as current_group) = function
    [] -> [current_group]
  | (v, c)::r ->
      if !c = n then
	group_same_occ (n, v::vl) r
      else
	(n, vl) :: (group_same_occ (!c, [v]) r)
	

let rec remove_n_times simp_facts n a l = 
  if n = 0 then l else
  match l with
    [] -> raise Not_found
  | a'::l' ->
      if simp_equal_terms simp_facts true a a' then
	remove_n_times simp_facts (n-1) a l'
      else
	a' :: (remove_n_times simp_facts n a l')

(* [sep_at_least_occ simp_facts n l] returns a pair [(l1,l2)] where
   [l] contains at least [n] times the elements in [l1], and [l2]
   consists of the remaining elements of [l]: the elements of [l] are
   [n] times the elements of [l1] plus the elements of [l2]; [l2]
   never contains [n] times the same element. *)

let rec sep_at_least_occ simp_facts n = function
    [] -> [], []
  | a::l ->
      try 
	let l' = remove_n_times simp_facts (n-1) a l in
	let (at_least_n, not_at_least_n) = sep_at_least_occ simp_facts n l' in
	(a::at_least_n, not_at_least_n)
      with Not_found ->
	let (at_least_n, not_at_least_n) = sep_at_least_occ simp_facts n l in
	(at_least_n, a::not_at_least_n)

(* [append_n_times accu n l] returns the concatenation
   of [n] copies of [l] and [accu]. (Assumes n >= 0.) *)

let rec append_n_times accu n l =
  if n = 0 then
    accu 
  else
    append_n_times (l @ accu) (n-1) l

(* [split_n next_f [] [] n l] splits the list [l] into a list of [n]
   elements and the rest, and calls [next_f] with the two lists. When
   [next_f] raises [NoMatch], try another partition of [l] (with the
   same numbers of elements).  Raises [NoMatch] when no partition
   works.

   Inside the induction, [split_n next_f n_part rest n l] splits the
   list [l] into a list [l1] of [n] elements and the rest [l2], and
   calls [next_f] with [l1 @ n_part] and [l2 @ rest] (reversed).
 *)

let rec split_n match_error next_f n_part rest n l =
  if n = 0 then
    next_f n_part (List.rev_append rest l)
  else
    match l with
      [] -> match_error()
    | a::r ->
	try 
	  split_n match_error next_f (a::n_part) rest (n-1) r
	with NoMatch ->
	  if List.length r < n then match_error() else
	  split_n match_error next_f n_part (a::rest) n r 


(* [match_AC match_term get_var_link match_error next_f simp_facts prod allow_rest l1 l2 state]
   matches the lists [l1] and [l2] modulo AC. 
   When [allow_rest] is false, it calls [next_f [] state'] after linking variables in [l1]
   so that [\sigma l1 = l2] modulo AC. 
   When [allow_rest] is true, it calls [next_f lrest state']  after linking variables in [l1]
   so that [\sigma l1 . lrest = l2] modulo AC. *)

let match_AC match_term get_var_link match_error next_f simp_facts prod allow_rest l1 l2 state =
  let has_neut = prod_has_neut prod in
  if (not has_neut) && (List.length l1 > List.length l2) then match_error() else 

  let rec split_among_vars_with_possible_rest next_f vl l state =
    match vl with
      [] -> next_f l state
    | v :: rest_vl ->
      (* Split [l] into two disjoint subsets, one that matches [v], the other that
	 matches [rest_vl]. We start with [l] matching [v] and the empty list matching
	 [rest_vl], and continue with fewer and fewer elements matching [v]. *)
	let len_l = List.length l in
	let allow_neut = 
	  match get_var_link v state with
	    None -> Parsing_helper.internal_error "get_var_link should return a link"
	  | Some(_, allow_neut) -> allow_neut
	in
	let rec partition_n n =
	  (* Considers a partition in which a sublist of [l] of [n] elements matches
	     [rest_vl] and the rest of [l], of [len_l - n] elements matches [v]. *) 
	  if n > len_l then match_error() else
	  if (n = len_l) && (not (has_neut && allow_neut)) then match_error() else
	  try 
	    split_n match_error (fun n_elem rest ->
	      match_term (split_among_vars_with_possible_rest next_f rest_vl n_elem) v (make_prod prod rest) state
		) [] [] n l
	  with NoMatch ->
	    partition_n (n+1)
	in
	partition_n 0
  in

  let rec match_variable_groups next_f g l2 state =
    match g with
      [] -> final_step match_error next_f allow_rest l2 state
    | (c, vl) :: rest ->
        (* Separate l2 into the elements that are present at least
	   [c] times and the others *)
	if c > 1 then
	  let (at_least_c, not_at_least_c) = sep_at_least_occ simp_facts c l2 in
	  split_among_vars_with_possible_rest (fun rest_l2 state' ->
	    let real_rest_l2 = append_n_times not_at_least_c c rest_l2 in
	    match_variable_groups next_f g real_rest_l2 state'
	      )  vl at_least_c state
	else
	  begin
	    assert(rest == []);
	    split_among_vars_with_possible_rest (final_step match_error next_f allow_rest) vl l2 state
	  end
  in
  
  let rec match_remaining_vars next_f remaining_vars l2 state =
    match remaining_vars with
      [] -> 
	final_step match_error next_f allow_rest l2 state
    | [t] when not allow_rest ->
	let allow_neut = 
	  match get_var_link t state with
	    None -> Parsing_helper.internal_error "get_var_link should return a link"
	  | Some(_, allow_neut) -> allow_neut
	in
	if (not (has_neut && allow_neut)) && (l2 == []) then match_error() else
	match_term (next_f []) t (make_prod prod l2) state
    | _ -> 
        (* Count the number of occurrences of variables in [remaining_vars] *)
	let var_occs = count_occ [] remaining_vars in
        (* Sort the variables in decreasing number of occurrences *)
	let var_occs_sorted = List.sort (fun (v1, c1) (v2, c2) -> (!c2) - (!c1)) var_occs in
	match var_occs_sorted with
          (vmax, cmax) :: rest ->
	    let g = group_same_occ (!cmax, [vmax]) rest in
	    match_variable_groups next_f g l2 state
	| _ -> Parsing_helper.internal_error "Should have at least one variable"	
  in

  let rec match_AC_rec next_f remaining_vars l1 l2 state =
    match l1 with
      [] -> 
	if List.exists (fun t -> 
	  match get_var_link t state with 
	    Some (TLink _, _) -> true
	  | _ -> false) remaining_vars then
	  match_AC_rec next_f [] remaining_vars l2 state
	else
	  match_remaining_vars next_f remaining_vars l2 state
    | t1::r1 ->
	match get_var_link t1 state with
	  None ->
	    (* Try to match t1 with an element of l2, and 
	       r1 with the rest of l2. *)
	    let rec try_list seen = function
		[] -> match_error()
	      | t2::r2 ->
		  let l2' = List.rev_append seen r2 in
		  try
		    match_term (match_AC_rec next_f remaining_vars r1 l2') t1 t2 state
		  with NoMatch ->
		    try_list (t2::seen) r2
	    in
	    try_list [] l2
	| Some (TLink t, _) ->
	    let l1' = simp_prod simp_facts (ref false) prod t in
	    begin
	      try 
		let r2 = multiset_minus simp_facts l2 l1' in
		match_AC_rec next_f remaining_vars r1 r2 state
	      with Not_found -> match_error()
	    end
	| Some (NoLink, _) ->
	    match_AC_rec next_f (t1::remaining_vars) r1 l2 state
  in

  match_AC_rec next_f [] l1 l2 state

(* Match term list *)

let rec match_term_list match_term next_f l l' state = 
  match l,l' with
    [],[] -> next_f state
  | a::l,a'::l' ->
      match_term (match_term_list match_term next_f l l') a a' state
  | _ -> Parsing_helper.internal_error "Different lengths in match_term_list"

(* Match function application *)

let match_funapp match_term get_var_link match_error simp_facts next_f t t' state =
  if t.t_type != t'.t_type then match_error() else
  let t'' = try_no_var simp_facts t' in
  match t.t_desc, t''.t_desc with
  | FunApp(f, [t1;t2]), FunApp(f', [t1';t2']) when 
    f == f' && (f.f_cat == Equal || f.f_cat == Diff) ->
	(* It is important to test this case before the commutative
	   function symbols: = and <> are also commutative function
	   symbols. *)
      begin
	match (match get_prod_list try_no_var_id [t1;t2] with
	         NoEq -> get_prod_list (try_no_var simp_facts) [t1';t2']
	       | x -> x)
	with
	  ACUN(xor,_) ->
	    match_term next_f (app xor [t1;t2]) (app xor [t1';t2']) state
	| CommutGroup(prod,inv,_) ->
	    begin
	      try
		match_term next_f (app prod [t1; app inv [t2]])
		  (app prod [t1'; app inv [t2']]) state
	      with NoMatch ->
		match_term next_f (app prod [t1; app inv [t2]])
		  (app prod [t2'; app inv [t1']]) state
	    end
        | Group(prod,inv,neut) -> 
            begin
	      let l1 = simp_prod simp_facts_id (ref false) prod (app prod [t1; app inv [t2]]) in
	      let l2 = remove_inverse_ends simp_facts_id (ref false) (prod, inv, neut) l1 in
	      let l1' = simp_prod simp_facts (ref false) prod (app prod [t1'; app inv [t2']]) in
	      let l2' = remove_inverse_ends simp_facts (ref false) (prod, inv, neut) l1' in
	      let rec match_assoc_up_to_roll seen' rest' =
		try
		  match_assoc match_term get_var_link match_error (fun _ state -> next_f state) simp_facts prod false l2 (rest' @ (List.rev seen')) state
		with NoMatch ->
		  match rest' with
		    [] -> match_error()
		  | a::rest'' ->
		      match_assoc_up_to_roll (a::seen') rest''
	      in
	      try
		match_assoc_up_to_roll [] l2'
	      with NoMatch ->
		let l3' = List.rev (List.map (compute_inv (try_no_var simp_facts) (ref false) (prod, inv, neut)) l2') in
		match_assoc_up_to_roll [] l3'
	    end
	| _ -> 
	    (* Fall back to the basic commutativity case when there is
	       no product. *)
            try
	      match_term (match_term next_f t2 t2') t1 t1' state
            with NoMatch ->
              match_term (match_term next_f t2 t1') t1 t2' state
      end
  | FunApp(f, [t1; t2]), FunApp(f', [t1';t2']) when (f == f') && (f.f_eq_theories = Commut) ->
      begin
        try
	  match_term (match_term next_f t2 t2') t1 t1' state
        with NoMatch ->
          match_term (match_term next_f t2 t1') t1 t2' state
      end
  | FunApp({f_eq_theories = (Group(f,inv',n) | CommutGroup(f,inv',n)) } as inv, [t]), _ when inv' == inv ->
      let t''inv = compute_inv (try_no_var simp_facts) (ref false) (f,inv,n) t'' in
      match_term next_f t t''inv state
  | FunApp(f,[_;_]),_ when f.f_eq_theories != NoEq && f.f_eq_theories != Commut ->
      (* f is a binary function with an equational theory that is
	 not commutativity -> it is a product-like function *)
      begin
	let l = simp_prod simp_facts_id (ref false) f t in
	let l' = simp_prod simp_facts (ref false) f t'' in
	match f.f_eq_theories with
	  NoEq | Commut -> Parsing_helper.internal_error "Terms.match_funapp: cases NoEq, Commut should have been eliminated"
	| AssocCommut | AssocCommutN _ | CommutGroup _ | ACUN _ ->
	    (* Commutative equational theories: use matching modulo AC *)
	    match_AC match_term get_var_link match_error (fun _ state -> next_f state) simp_facts f false l l' state
	| Assoc | AssocN _ | Group _ -> 
	    (* Non-commutative equational theories: use matching modulo associativity *)
	    match_assoc match_term get_var_link match_error (fun _ state -> next_f state) simp_facts f false l l' state
	      (* Above, I ignore on purpose group and XOR properties,
		 they would yield too general and counter-intuitive matchings. *)
      end
  | FunApp(f,l), FunApp(f',l') when f == f' ->
      match_term_list match_term next_f l l' state
  | _ -> match_error()


(*********** Matching modulo equational theory, with advice *************)
(*********** for use in transf_crypto.ml                    *************)

(* Common arguments for the matching functions:

   [match_term]: [match_term next_f t1 t2 state] matches [t1] with [t2];
   calls [next_f state'] when the match succeeds; raises NoMatch when it
   fails. It must clean up the links it has put at least when it fails.
   (When it succeeds, the cleanup is optional.)

   [explicit_value]: [explicit_value t state] returns a state in which 
   the advice needed to instantiate the variable [t] has been recorded.
   Causes an internal error when [t] is not a variable.

   [get_var_link]: [get_var_link t state] returns [Some (link, allow_neut)]
   when [t] is variable that can be bound by a product of terms,
   [link] is the current contents of the link of that variable,
   [allow_neut] is true if and only if the variable may be bound to
   the neutral element (provided there is a neutral element for the
   product); it returns [None] otherwise.

   [is_var_inst]: [is_var_inst t] returns [true] when [t] is a variable
   that can be instantiated by applying advice.

   [simp_facts] collects the rewrite rules corresponding to known equalities
   and other known facts, which we use in order to replace variables with their values and
   to test equality between terms.

   [prod] is the product function symbol, which is associative or AC.
   *)

(* Matching modulo associativity, plus perhaps neutral element *)


(* [match_assoc_advice match_term explicit_value get_var_link is_var_inst fresh_vars_init next_f simp_facts prod l1 l2 state]
   matches the lists [l1] and [l2] modulo associativity. 
   It calls [next_f state'] after linking variables in [l1]
   so that [\sigma l1 = l2] modulo associativity.

   [fresh_vars_init] contains fresh variables created for the matching.

   [match_assoc_advice] is programmed like unification modulo associativity, 
   because in the second term, variables may be instantiated by advice. 

   For this to work, either the function match_term must also be programmed as
   unification (i.e. be invariant by swapping l1 and l2). This would imply modifying
   check_instance_of_rec, match_funapp, match_AC. 
   Or we need a reliable way to attribute each element to its source (the pattern
   or the instance), to call match_term in the right direction. When both
   elements come from the instance, we can just test equality. Both elements
   cannot come from the pattern, because we do not put explicit links in the
   advice variables. We have chosen this second implementation. *)

type var_type =
    Fresh | Advice | Pat

let special_neut_symb = 
  { f_name = "$@special_neut";
    f_type = [], Settings.t_any;
    f_cat = Std;
    f_options = 0;
    f_statements = [];
    f_collisions = [];
    f_eq_theories = NoEq;
    f_impl = No_impl;
    f_impl_inv = None }

let special_neut_term = 
  build_term_type Settings.t_any (FunApp(special_neut_symb, []))

let match_assoc_advice match_term explicit_value get_var_link is_var_inst fresh_vars_init next_f simp_facts prod l1 l2 state =
  (* [has_neut] is true iff there is a neutral element for the product [prod]. *)
  let has_neut = prod_has_neut prod in

  let fresh_vars = ref (List.map fst fresh_vars_init) in

  (* is_rev is true when the lists l1 and l2 have been reversed.
     In this case, when a variable is assigned or read, its content
     must also be reversed. *)
  let put_side is_rev s l =
    List.map (fun t ->
      match t.t_desc with
	Var(b,_) when List.memq b (!fresh_vars) -> (Fresh, t)
      |	_ -> (s, t)) (if is_rev then List.rev l else l)
  in

  (*
   [get_var_link_unif]: [get_var_link_unif t state] returns 
   [Some(link, allow_neut, var_advice, shortest)] when [t] is a variable
   can that be bound to a product using [prod]. 
   [link] is the current link of that variable.
   [allow_neut] is true if and only if that variable may be bound to 
   the neutral element of the product [prod] (when it has a neutral element).
   [var_advice] is true if and only if the variable is to be 
   instantiated using advice. 
   [shortest] is true if and only if we should try first to 
   instantiate the variable with a product containing as few terms
   as possible.
   Otherwise, [get_var_link_unif] returns None.
   The function [get_var_link_unif] is programmed using
   the functions [get_var_link] and [is_var_inst].
  *)

  let get_var_link_unif (side, t) state =
    (* fresh variables created during the matching *)
    match side with
      Fresh ->
	begin
	  match t.t_desc with
	    Var(b,_) -> Some(b.link, 
			     (try
			       List.assq b fresh_vars_init
			     with Not_found -> false), 
			     Fresh, true)
	  | _ -> Parsing_helper.internal_error "get_var_link_unif: Fresh variables should be variables!"
	end
    | Advice ->
      (* variables are advice variables *)
	if is_var_inst t then
	  Some(NoLink, true, Advice, true)
	else
	  None
    | Pat ->
      (* variables are variables from the pattern *)
	match get_var_link t state with
	  None -> None
	| Some(l, allow_neut) -> 
	    Some(l, allow_neut, Pat, false)
  in

  let assign_var is_rev next_f allow_neut (side, tvar) l state =
    match tvar.t_desc with
      Var(b,_) -> 
	begin
          (* check that tvar does not occur in l! *)
	  if List.exists (fun (_,t) -> refers_to b t) l then
	    raise NoMatch;
	  match side with
	    Advice -> 
	      if (not (has_neut && allow_neut)) && (l == []) then raise NoMatch;
	      next_f (explicit_value tvar state)
	  | Fresh ->
	      (* For fresh variables created in match_assoc_advice_subterm, 
		 we may create a special neutral element
		 when there is no neutral element *)
	      if (not allow_neut) && (l == []) then raise NoMatch;
	      if List.exists (fun (side,_) -> side == Pat) l then
		(* Ignore the link when it points to a Pat term, so
                   that, when we will expend the link, we can give it
		   side Advice (or Fresh when it is a fresh variable).
		   TO DO I'm not entirely sure if this can happen for variables
		   other than the two variables b_left and b_right that come
		   from match_assoc_advice_pat_subterm.
		   Perhaps I could raise an internal error for the other variables... *)
		next_f state
	      else
		let tval = 
                  if (not has_neut) && (l == []) then special_neut_term else
                  make_prod prod (List.map snd (if is_rev then List.rev l else l)) 
                in
		auto_cleanup (fun () ->
		  link b (TLink tval);
		  next_f state
		    )
	  | Pat ->
	      if (not (has_neut && allow_neut)) && (l == []) then raise NoMatch;
	      if List.exists (fun (side,_) -> side == Pat) l then
		Parsing_helper.internal_error "Pat variables should be linked to non-Pat terms";
	      let tval = make_prod prod (List.map snd (if is_rev then List.rev l else l)) in	      
	      match_term next_f tvar tval state
	end
    | _ -> Parsing_helper.internal_error "assign_var: Variable expected"
  in

  let match_term_orient next_f (side1,t1) (side2,t2) state =
    match side1, side2 with
      Fresh, _ | _, Fresh -> Parsing_helper.internal_error "match_term_orient: Fresh variables should have been treated before"
    | Advice, Advice ->
	if not (simp_equal_terms simp_facts true t1 t2) then raise NoMatch;
	next_f state
    | Advice, Pat -> match_term next_f t2 t1 state
    | Pat, Advice -> match_term next_f t1 t2 state
    | Pat, Pat -> Parsing_helper.internal_error "match_term_orient: terms should not come both from the pattern"
  in

  (* Invariant: one of the two lists [l1] (with [tvar] in [try_prefix]) or 
     [l2] (with [seen] in [try_prefix]) entirely comes from the game
     (all its elements have side Advice or Fresh). The other list may 
     contain a mix of sides Pat, Advice, and Fresh, since links
     from Pat to Advice may be replaced with their content. *)

  (* try to match [tvar . l1 = seen . l2] where [tvar] is a variable *)

  let rec try_prefix is_rev tvar l1 seen l2 state =
    match get_var_link_unif tvar state with
      None | Some(TLink _,_,_,_) -> Parsing_helper.internal_error "try_prefix: Should be a variable"
    | Some(NoLink, allow_neut, var_type, shortest) ->
	try 
	  if shortest then
	    try
            (* tvar = seen *)
	      assign_var is_rev (match_assoc_rec is_rev l1 l2) allow_neut tvar seen state
	    with NoMatch ->
              (* If it does not work, try with one more element *)
	      match l2 with
		[] -> raise NoMatch
	      | a::r -> try_prefix is_rev tvar l1 (seen @ [a]) r state
	  else
	    (* For variables of the pattern (shortest = false),
	       I try the prefixes by first trying l2 entirely, then removing the
	       last element of l2, etc. until I try the empty list. 
	       The reason for this order is that, in case we match a subterm of the
	       product, we want to take the largest possible subterm that works. *)
	    try 
	      match l2 with
		[] -> raise NoMatch
	      | a::r -> try_prefix is_rev tvar l1 (seen @ [a]) r state
	    with NoMatch ->
              (* tvar = seen *)
	      assign_var is_rev (match_assoc_rec is_rev l1 l2) allow_neut tvar seen state
	with NoMatch ->
	  match l2 with
	    [] -> raise NoMatch
	  | a::r -> 
	      match get_var_link_unif a state with
		None -> raise NoMatch
	      | Some(TLink t, _, _, _) -> 
		  let l2' = simp_prod simp_facts (ref false) prod t in
		  try_prefix is_rev tvar l1 seen ((put_side is_rev Advice l2') @ r) state
	      | Some(NoLink, allow_neut, _, _) ->
		  let x = create_binder "@$match_var" (new_vname()) (snd prod.f_type) [] in
		  fresh_vars := x :: (!fresh_vars);
		  let x_term = term_from_binder x in
	          (* tvar = seen . x ; a = x . (some prefix of l1 to be defined) *)
		  assign_var is_rev (try_prefix is_rev a r [Fresh,x_term] l1) 
		    allow_neut tvar (seen @ [Fresh,x_term]) state
		    
  and match_var is_rev status1 l1 l2 state =
    match l1 with
      [] -> Parsing_helper.internal_error "match_var: l1 should not be empty"
    | t1::r1 ->
    match status1 with
      None | Some (TLink _, _, _, _) -> Parsing_helper.internal_error "match_var: get_var_link_unif should be Some(NoLink, ...)"
    | Some (NoLink, allow_neut, var_type, shortest) ->
	match l2 with
	  t2::r2 when simp_equal_terms simp_facts true (snd t1) (snd t2) -> 
	    match_assoc_rec is_rev r1 r2 state
	| _ ->
	    if (r1 == []) then
	      begin
	        (* If variable t1 is alone, that's easy: t1 should be linked to l2 *)
		assign_var is_rev next_f allow_neut t1 l2 state
	      end
	    else
	      begin
	        (* try to see if the end of the list contains something that is not an unbound variable *)
		let l1rev = List.rev l1 in
		let l2rev = List.rev l2 in
		if (match get_var_link_unif (List.hd l1rev) state with
		     Some (NoLink, _, _, _) -> true
		   | _ -> false) ||
		     ((l2 != []) && 
		      (match get_var_link_unif (List.hd l2rev) state with
			Some (NoLink, _, _, _) -> true
		      | _ -> false))
		then
		  (* l1 starts and ends with a variable, I really need to try all prefixes
		     of l2 as values for variable v. That can be costly. *)
		  try_prefix is_rev t1 r1 [] l2 state
		else
		  match_assoc_rec (not is_rev) l1rev l2rev state
	      end

  and match_assoc_rec is_rev l1 l2 state =
    let status1 =
      match l1 with
	[] -> None
      |	t1::_ -> get_var_link_unif t1 state
    in
    let status2 =
      match l2 with
	[] -> None
      |	t2::_ -> get_var_link_unif t2 state
    in
    match l1, status1, l2, status2 with
    | [], _, [], _ -> next_f state 
    | t1::r1, Some(TLink t,_,_,_), _, _ ->
	let l1' = simp_prod simp_facts (ref false) prod t in
	match_assoc_rec is_rev ((put_side is_rev Advice l1') @ r1) l2 state
    | _, _, t2::r2, Some(TLink t,_,_,_) ->
	let l2' = simp_prod simp_facts (ref false) prod t in
	match_assoc_rec is_rev l1 ((put_side is_rev Advice l2') @ r2) state
    | t1::r1, Some(NoLink,_,(Pat|Fresh),_), _, _ ->
	match_var is_rev status1 l1 l2 state
    | _, _, t2::r2, Some(NoLink,_,(Pat|Fresh),_) ->
	match_var is_rev status2 l2 l1 state
    | t1::r1, Some(NoLink,_,Advice,_), _, _ ->
	match_var is_rev status1 l1 l2 state
    | _, _, t2::r2, Some(NoLink,_,Advice,_) ->
	match_var is_rev status2 l2 l1 state
    | [], _, _, _ -> raise NoMatch
    | _, _, [], _ -> raise NoMatch
    | t1::r1, _, t2::r2, _ -> 
	match_term_orient (match_assoc_rec is_rev r1 r2) t1 t2 state

  in
  match_assoc_rec false (put_side false Pat l1) (put_side false Advice l2) state
		    
(* [match_assoc_advice_subterm match_term explicit_value get_var_link is_var_inst next_f simp_facts prod l1 l2 state]
   matches the lists [l1] and [l2] modulo associativity. 
   More precisely, it calls [next_f left_rest right_rest state']  after linking variables in [l1]
   so that [left_rest. \sigma l1 . right_rest = l2] modulo associativity. *)

let match_assoc_advice_subterm match_term explicit_value get_var_link is_var_inst next_f simp_facts prod l1 l2 state =
  let b_right = create_binder "@$special_var_allow_rest" (new_vname()) (snd prod.f_type) [] in
  let b_left = create_binder "@$special_var_allow_rest" (new_vname()) (snd prod.f_type) [] in
  let l1' = term_from_binder b_left :: l1 @ [term_from_binder b_right] in
  let next_f_unif state = 
    let right_rest = 
      match b_right.link with
	NoLink -> []
      | TLink t -> 
	  if t == special_neut_term then [] else
	  simp_prod simp_facts (ref false) prod t
    in
    let left_rest = 
      match b_left.link with
	NoLink -> []
      | TLink t -> 
	  if t == special_neut_term then [] else
	  simp_prod simp_facts (ref false) prod t
    in
    next_f left_rest right_rest state
  in
  (* the variables b_right and b_left can ALWAYS be bound to the neutral element
     (even if there is in fact no neutral element! In this case, we use the special
     term special_neut_term instead) because I want to be able to match the full term *)
  match_assoc_advice match_term explicit_value get_var_link is_var_inst [(b_left, true); (b_right, true)] next_f_unif simp_facts prod l1' l2 state 

(* [match_assoc_advice_pat_subterm match_term explicit_value get_var_link is_var_inst next_f prod allow_full l1 l2 state]
   matches the lists [l1] and [l2] modulo associativity. 
   More precisely, it calls [next_f state']  after linking variables in [l1]
   so that [\sigma l1 = left_rest . l2 . right_rest] modulo associativity.
   [left_rest] and [right_rest] are just ignored, they are not passed to [next_f].
   [allow_full] is true when [l2] may match the full list [l1], that is,
   [left_rest] and [right_rest] may both be empty. *)

let match_assoc_advice_pat_subterm match_term explicit_value get_var_link is_var_inst next_f simp_facts prod allow_full l1 l2 state =
  let b_right = create_binder "@$special_var_allow_rest" (new_vname()) (snd prod.f_type) [] in
  let b_left = create_binder "@$special_var_allow_rest" (new_vname()) (snd prod.f_type) [] in
  let l2' = term_from_binder b_left :: l2 @ [term_from_binder b_right] in
  (* the variables b_right and b_left must not be both bound to the 
     neutral element because I want to match a strict subterm *)
  let is_neut t =
    (t == special_neut_term) ||
    (match prod.f_eq_theories, t.t_desc with
       (Group(_,_,n) | CommutGroup(_,_,n) | AssocN(_,n) 
        | AssocCommutN(_,n) | ACUN(_,n)), FunApp(n',[]) -> n == n'
    | _ -> false)
  in
  let next_f_unif state =
    if not allow_full then
      begin
	match b_left.link, b_right.link with
	  TLink t_left, TLink t_right ->
	    if (is_neut t_left) && (is_neut t_right) then raise NoMatch
	| _ -> ()
      end;
    next_f state
  in
  match_assoc_advice match_term explicit_value get_var_link is_var_inst [(b_left, true); (b_right, true)] next_f_unif simp_facts prod l1 l2' state 

(* Matching modulo associativity and commutativity, plus perhaps neutral element *)

(* [match_AC_advice match_term explicit_value get_var_link is_var_inst next_f simp_facts prod allow_rest_pat allow_full allow_rest l1 l2 state]
   matches the lists [l1] and [l2] modulo AC. 
   When [allow_rest] and [allow_rest_pat] are false, it calls [next_f [] state'] after linking variables in [l1]
   so that [\sigma l1 = l2] modulo AC. 
   When [allow_rest] is true and [allow_rest_pat] is false, it calls [next_f lrest state']  after linking variables in [l1]
   so that [\sigma l1 . lrest = l2] modulo AC. 
   When [allow_rest] is false and [allow_rest_pat] is true, it calls [next_f [] state']  after linking variables in [l1]
   so that [\sigma l1 = l2 . lrest] modulo AC. [lrest] must not be empty; it is ignored, it is not passed to [next_f].

   [allow_rest_pat] is true when a subterm of the pattern in [l1] should match
   [l2], so that some elements of [l1] are allowed to remain unmatched.

   In case [allow_rest_pat] is true, [allow_full] is true when [l2] may match the 
   full list [l1], that is, [lrest] may be empty.

   [allow_rest] is true when the pattern in [l1] should match a subterm of 
   the term in [l2], so that some elements of [l2] are allowed to remain unmatched.
*)

let match_AC_advice match_term explicit_value get_var_link is_var_inst next_f simp_facts prod allow_rest_pat allow_full allow_rest l1 l2 state =
  let has_neut = prod_has_neut prod in

  let final_step next_f l2 state =
    if (l2 == []) || allow_rest then next_f l2 state else raise NoMatch
  in

  let rec all_possible_explicit_value l state =
    match l with
      [] -> state
    | t::r ->
	if is_var_inst t then
	  all_possible_explicit_value r (explicit_value t state)
	else
	  all_possible_explicit_value r state
  in

  let rec split_among_vars_with_possible_rest next_f vl l state =
    match vl with
      [] -> next_f l state
    | v :: rest_vl ->
      (* Split [l] into two disjoint subsets, one that matches [v], the other that
	 matches [rest_vl]. We start with [l] matching [v] and the empty list matching
	 [rest_vl], and continue with fewer and fewer elements matching [v]. *)
	let len_l = List.length l in
	let allow_neut = 
	  match get_var_link v state with
	    None -> Parsing_helper.internal_error "get_var_link should return a link"
	  | Some(_, allow_neut) -> allow_neut
	in
	let rec partition_n n =
	  (* Considers a partition in which a sublist of [l] of [n] elements matches
	     [rest_vl] and the rest of [l], of [len_l - n] elements matches [v]. *) 
	  if n > len_l then raise NoMatch else
	  if (n = len_l) && (not (has_neut && allow_neut)) then raise NoMatch else
	  try 
	    split_n default_match_error (fun n_elem rest ->
	      match_term (split_among_vars_with_possible_rest next_f rest_vl n_elem) v (make_prod prod rest) state
		) [] [] n l
	  with NoMatch ->
	    partition_n (n+1)
	in
	partition_n 0
  in

  let rec match_variable_groups next_f g l2 state =
    match g with
      [] -> final_step next_f l2 state
    | (c, vl) :: rest ->
        (* Separate l2 into the elements that are present at least
	   [c] times and the others *)
	if c > 1 then
	  let (at_least_c, not_at_least_c) = sep_at_least_occ simp_facts c l2 in
	  split_among_vars_with_possible_rest (fun rest_l2 state' ->
	    let real_rest_l2 = append_n_times not_at_least_c c rest_l2 in
	    match_variable_groups next_f g real_rest_l2 state'
	      )  vl at_least_c state
	else
	  begin
	    assert(rest == []);
	    split_among_vars_with_possible_rest (final_step next_f) vl l2 state
	  end
  in
  
  let rec match_remaining_vars next_f remaining_vars l2 state =
    match remaining_vars with
      [] -> 
	final_step next_f l2 state
    | [t] when not allow_rest ->
	let allow_neut = 
	  match get_var_link t state with
	    None -> Parsing_helper.internal_error "get_var_link should return a link"
	  | Some(_, allow_neut) -> allow_neut
	in
	if (not (has_neut && allow_neut)) && (l2 == []) then raise NoMatch else
	match_term (next_f []) t (make_prod prod l2) state
    | _ -> 
        (* Count the number of occurrences of variables in [remaining_vars] *)
	let var_occs = count_occ [] remaining_vars in
        (* Sort the variables in decreasing number of occurrences *)
	let var_occs_sorted = List.sort (fun (v1, c1) (v2, c2) -> (!c2) - (!c1)) var_occs in
	match var_occs_sorted with
          (vmax, cmax) :: rest ->
	    let g = group_same_occ (!cmax, [vmax]) rest in
	    match_variable_groups next_f g l2 state
	| _ -> Parsing_helper.internal_error "Should have at least one variable"	
  in

  let rec match_AC_rec next_f advice_delayed remaining_vars l1 l2 state =
    match l1 with
      [] -> 
	if List.exists (fun t -> 
	  match get_var_link t state with 
	    Some (TLink _, _) -> true
	  | _ -> false) remaining_vars then
	  match_AC_rec next_f advice_delayed [] remaining_vars l2 state
	else
	  begin
	    try
	      if advice_delayed != [] then raise NoMatch;
	      if allow_rest_pat then raise NoMatch; (* This case is handled below *)
	      match_remaining_vars next_f remaining_vars l2 state
	    with NoMatch ->
	      (* advice_delayed and remaining_vars must match the elements of l2 *)
	      let (with_advice, without_advice) = List.partition is_var_inst l2 in
	      if (with_advice = []) && not allow_rest_pat then 
		(* there remains unmatched elements in l1, the elements of [advice_delayed] and [remaining_vars],
		   except in case they are both empty. In this case, [allow_rest = false] and [l2 != []], otherwise
		   [match_remaining_vars] would have succeeded; since [with_advice = []], [without_advice != []],
		   so in this case, there remains unmatched elements in l2, the elements of [without_advice]. *)
		raise NoMatch;
	      if without_advice != [] && (not allow_rest) && remaining_vars = [] then 
		(* there remains unmatched elements in l2, the elements of [without_advice] *)
		raise NoMatch;
	      if advice_delayed == [] && remaining_vars == [] && (allow_rest_pat && not allow_full) then 
		(* the rest of the pattern would be empty, this is not allowed *)
		raise NoMatch;
	      if allow_rest && (remaining_vars = []) then
		(* Since there are no remaining variables, at least the terms
		   in [without_advice] cannot be matched by the expression,
		   so they end up in the rest part passed to next_f. *)
		next_f without_advice (all_possible_explicit_value with_advice state)
	      else 
		next_f [] (all_possible_explicit_value with_advice state)
	  end
    | t1::r1 ->
	match get_var_link t1 state with
	  None ->
	    (* Try to match t1 with an element of l2, and 
	       r1 with the rest of l2. *)
	    let rec try_list seen = function
		[] -> 
		  (* In case an element of l2 may be instantiated by
		     advice, delay the treatment of t1 *)
		  if allow_rest_pat || (List.exists is_var_inst l2) then
		    match_AC_rec next_f (t1::advice_delayed) remaining_vars r1 l2 state
		  else
		    raise NoMatch
	      | t2::r2 ->
		  let l2' = List.rev_append seen r2 in
		  try
		    match_term (match_AC_rec next_f advice_delayed remaining_vars r1 l2') t1 t2 state
		  with NoMatch ->
		    try_list (t2::seen) r2
	    in
	    try_list [] l2
	| Some (TLink t, _) ->
	    let l1' = simp_prod simp_facts (ref false) prod t in
	    begin
	      try 
		let r2 = multiset_minus simp_facts l2 l1' in
		match_AC_rec next_f advice_delayed remaining_vars r1 r2 state
	      with Not_found -> 
		(* In case an element of l2 may be instantiated by
		   advice, delay the treatment of t1 *)
		if allow_rest_pat || (List.exists is_var_inst l2) then
		  match_AC_rec next_f (t1::advice_delayed) remaining_vars r1 l2 state
		else
		  raise NoMatch
	    end
	| Some (NoLink, _) ->
	    match_AC_rec next_f advice_delayed (t1::remaining_vars) r1 l2 state
  in
  
  match_AC_rec next_f [] [] l1 l2 state

(* Match function application *)

let match_funapp_advice match_term explicit_value get_var_link is_var_inst next_f simp_facts t t' state =
  if t.t_type != t'.t_type then raise NoMatch else
  match t.t_desc, t'.t_desc with
  | FunApp(f, [t1;t2]), FunApp(f', [t1';t2']) when 
    f == f' && (f.f_cat == Equal || f.f_cat == Diff) ->
	(* It is important to test this case before the commutative
	   function symbols: = and <> are also commutative function
	   symbols. *)
      begin
	match (match get_prod_list (try_no_var simp_facts) [t1;t2] with
	         NoEq -> get_prod_list (try_no_var simp_facts) [t1';t2']
	       | x -> x)
	with
	  ACUN(xor,_) ->
	    match_term next_f (app xor [t1;t2]) (app xor [t1';t2']) state
	| CommutGroup(prod,inv,_) ->
	    begin
	      try
		match_term next_f (app prod [t1; app inv [t2]])
		  (app prod [t1'; app inv [t2']]) state
	      with NoMatch ->
		match_term next_f (app prod [t1; app inv [t2]])
		  (app prod [t2'; app inv [t1']]) state
	    end
        | Group(prod,inv,neut) -> 
            begin
	      let l1 = simp_prod simp_facts (ref false) prod (app prod [t1; app inv [t2]]) in
	      let l2 = remove_inverse_ends simp_facts (ref false) (prod, inv, neut) l1 in
	      let l1' = simp_prod simp_facts (ref false) prod (app prod [t1'; app inv [t2']]) in
	      let l2' = remove_inverse_ends simp_facts (ref false) (prod, inv, neut) l1' in
	      let rec match_assoc_up_to_roll seen' rest' =
		try
		  match_assoc_advice match_term explicit_value get_var_link is_var_inst [] next_f simp_facts prod l2 (rest' @ (List.rev seen')) state
		with NoMatch ->
		  match rest' with
		    [] -> raise NoMatch
		  | a::rest'' ->
		      match_assoc_up_to_roll (a::seen') rest''
	      in
	      try
		match_assoc_up_to_roll [] l2'
	      with NoMatch ->
		let l3' = List.rev (List.map (compute_inv (try_no_var simp_facts) (ref false) (prod, inv, neut)) l2') in
		match_assoc_up_to_roll [] l3'
	    end
	| _ -> 
	    (* Fall back to the basic commutativity case when there is
	       no product. *)
            try
	      match_term (match_term next_f t2 t2') t1 t1' state
            with NoMatch ->
              match_term (match_term next_f t2 t1') t1 t2' state
      end
  | FunApp(f, [t1; t2]), FunApp(f', [t1';t2']) when (f == f') && (f.f_eq_theories = Commut) ->
      begin
        try
	  match_term (match_term next_f t2 t2') t1 t1' state
        with NoMatch ->
          match_term (match_term next_f t2 t1') t1 t2' state
      end
  | FunApp({f_eq_theories = (Group(f,inv',n) | CommutGroup(f,inv',n)) } as inv, [t]), _ when inv' == inv ->
      let t''inv = compute_inv (try_no_var simp_facts) (ref false) (f,inv,n) t' in
      match_term next_f t t''inv state
  | FunApp(f,[_;_]),_ when f.f_eq_theories != NoEq && f.f_eq_theories != Commut ->
      (* f is a binary function with an equational theory that is
	 not commutativity -> it is a product-like function *)
      begin
	let l = simp_prod simp_facts (ref false) f t in
	let l' = simp_prod simp_facts (ref false) f t' in
	match f.f_eq_theories with
	  NoEq | Commut -> Parsing_helper.internal_error "Terms.match_funapp_advice: cases NoEq, Commut should have been eliminated"
	| AssocCommut | AssocCommutN _ | CommutGroup _ | ACUN _ ->
	    (* Commutative equational theories: use matching modulo AC *)
	    match_AC_advice match_term explicit_value get_var_link is_var_inst (fun _ state -> next_f state) simp_facts f false false false l l' state
	| Assoc | AssocN _ | Group _ -> 
	    (* Non-commutative equational theories: use matching modulo associativity *)
	    match_assoc_advice match_term explicit_value get_var_link is_var_inst [] next_f simp_facts f l l' state
	      (* Above, I ignore on purpose group and XOR properties,
		 they would yield too general and counter-intuitive matchings. *)
      end
  | FunApp(f,l), FunApp(f',l') when f == f' ->
      match_term_list match_term next_f l l' state
  | _ -> raise NoMatch
