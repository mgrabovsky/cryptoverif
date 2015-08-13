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

(* Basic list functions *)

(* [repeat n x] returns a list containing [n] copies of [x] *)
val repeat : int -> 'a -> 'a list

(* [skip n l] returns the list [l] without its [n] first elements.
   Raises an exception if [l] contains fewer than [n] elements *)
val skip : int -> 'a list -> 'a list

(* [split n l] splits [l] into two lists: the first [n] elements,
   and the rest.
   Raises an internal error if [l] contains fewer than [n] elements *)
val split : int -> 'a list -> ('a list * 'a list)

(* [find x l] looks for [x] in list [l], and returns its position. 
   (The first element has position 0.) 
   Raises Not_found if [x] does not occur in [l]. *)
val find_in_list : 'a -> 'a list -> int

(* [lsuffix n l] returns a suffix of [l] of length [n].
   Raises an exception if [l] contains fewer than [n] elements *)
val lsuffix : int -> 'a list -> 'a list

(* [remove_suffix n l] returns the list [l] without its last [n] elements.
   Raises an internal error if [l] contains fewer than [n] elements *)
val remove_suffix : int -> 'a list -> 'a list


(* Intersection / Union *)

(* [intersect eqtest l1 l2] returns the intersection of [l1] and [l2]
   considered as sets, where [eqtest] is used to test equality between
   elements. *)
val intersect : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list

(* [intersect_list eqtest l] returns the intersection of all lists
   in [l] (which is a list of lists), where [eqtest] is used to test
   equality between elements. 
   Raises Contradiction when [l] is the empty list. (The intersection
   should be the full set.) *)
val intersect_list : ('a -> 'a -> bool) -> 'a list list -> 'a list

(* [union eqtest l1 l2] returns the union of [l1] and [l2]
   considered as sets, where [eqtest] is used to test equality between
   elements. *)
val union : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list

(* [map_union eqtest f l] applies [f] to each element of [l]. 
   [f] returns a list, [map_union] then returns the union of all these
   lists, where [eqtest] is used to test equality between
   elements. *)
val map_union : ('b -> 'b -> bool) -> ('a -> 'b list) -> 'a list -> 'b list




val equal_lists : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
val equal_instruct : instruct -> instruct -> bool
val add_eq : instruct -> instruct list -> instruct list

val type_for_param : param -> typet
val param_from_type : typet -> param

val binder_from_term : term -> binder
val binderref_from_term : term -> binderref
val repl_index_from_term : term -> repl_index
val term_from_binder : binder -> term
val term_from_binderref : binderref -> term
val binderref_from_binder : binder -> binderref
val term_from_repl_index : repl_index -> term
val build_term : term -> term_desc -> term
val build_term2 : term -> term_desc -> term
val build_term_type : typet -> term_desc -> term

val iproc_from_desc : inputprocess_desc -> inputprocess
val oproc_from_desc : process_desc -> process
val iproc_from_desc2 : inputprocess -> inputprocess_desc -> inputprocess
val oproc_from_desc2 : process -> process_desc -> process

val app : funsymb -> term list -> term

val is_args_at_creation : binder -> term list -> bool

val cst_for_type : typet -> term

val is_restr : binder -> bool
val is_assign : binder -> bool

val current_bound_vars : binder list ref
val cleanup : unit -> unit
val link : binder -> linktype -> unit
val auto_cleanup : (unit -> 'a) -> 'a

(* [max_occ] is the maximum occurrence number seen so far.
   It is used to determine the left margin in the display of games,
   so that there is enough space to display occurrence numbers in 
   the margin *)
val max_occ : int ref
(* [new_occ()] returns a new occurrence number *)
val new_occ : unit -> int
(* [vcounter] is a variable counter, incremented to create a fresh variable. *)
val vcounter : int ref
val new_vname : unit -> int
val new_binder : binder -> binder
val new_repl_index : repl_index -> repl_index
val create_binder : string -> int -> typet -> repl_index list -> binder
val create_repl_index : string -> int -> typet -> repl_index

(* Copy a term, process, ..., substituting variables with their links.
   The substitution is performed in different ways, depending on
   the value of the argument [copy_transf]. *)
type copy_transf =
    Links_RI (* Substitutes replication indices that are linked *)
  | Links_Vars 
     (* Substitutes variables that are linked, when their arguments are args_at_creation
	The linked variables are supposed to be defined above the copied terms/processes *)
  | Links_RI_Vars (* Combines Links_RI and Links_Vars *)
  | OneSubst of binder * term * bool ref 
     (* [OneSubst(b,t,changed)] substitutes b[b.args_at_creation] with t.
	It sets [changed] to true when such a substitution has been done.
	[b] is assumed to be defined above the copied terms/processes *) 
  | OneSubstArgs of binderref * term 
     (* [OneSubstArgs(br,t)] substitutes [t] for the accesses [br].
	It is assumed that [br] and [t] are already guaranteed to be defined,
	so [br] is removed from defined conditions if it occurs. *)
  | Rename of term list * binder * binder
     (* Rename(args, b, b') replaces array accesses b[args] with b'[args] *)
  | Links_Vars_Args of (binder * binder) list
     (* Links_Vars_Args(replacement_def_list) substitutes variables that are 
	linked, for any arguments: if b is linked to M, b[l] is
	replaced with M{l/b.args_at_creation}. replacement_def_list defines
	variable replacements to do in defined conditions.
	This transformation is used in the removal of assignments. *)

val copy_binder : copy_transf -> binderref -> binderref (* For the transformation Rename only *)
val copy_term : copy_transf -> term -> term
val copy_pat : copy_transf -> pattern -> pattern
val copy_def_list : copy_transf -> binderref list -> binderref list
val copy_oprocess : copy_transf -> process -> process
val copy_process : copy_transf -> inputprocess -> inputprocess

(* [subst cur_array l t] returns the term [t] in which the replication
   indices in [cur_array] have been replaced with their corresponding
   term in [l]. 
   The lists [cur_array] and [l] must have the same length.

   [subst_def_list] and [subst_simp_facts] are similar functions for
   defined conditions and facts instead of terms. *)
val subst : repl_index list -> term list -> term -> term
val subst_def_list : repl_index list -> term list -> binderref list -> binderref list
val subst_simp_facts : repl_index list -> term list -> simp_facts -> simp_facts

(* [subst3 l t] returns the term [t] after applying the substitution
   defined by [l]: [l] is a list of pairs (variable, term), and [subst3]
   replaces each variable with the corresponding term. 

   [subst_def_list3] and [subst_oprocess3] are similar functions
   for defined conditions and processes instead of terms. *)
val subst3 : (binder * term) list -> term -> term
val subst_def_list3 : (binder * term) list -> binderref list -> binderref list
val subst_oprocess3 : (binder * term) list -> process -> process

(* Functions for manipulating terms with equations *)

(* Identity function, to be used as placeholder for
   a term simplification function when we don't want to do
   any simplification *)
val try_no_var_id : term -> term

(* [compute_inv try_no_var reduced (prod, inv, neut) t] computes the inverse of
   term [t].
   [prod] is the product function, [inv] is the inverse function,
   [neut] is the neutral element.
   [reduced] is set to true when [t] has been simplified.
   [try_no_var] is a function from terms to terms that tries to replace
   variables with their values. It leaves non-variable terms unchanged.
   It can be the identity when we do not have information on the values
   of variables. *)
val compute_inv : (term -> term) -> bool ref ->
  funsymb * funsymb * funsymb -> term -> term

(* Simplification function:
   [simp_prod try_no_var reduced sub_eq f t] simplifies term [t].
   [f] is a binary function with an equational theory. 
   [simp_prod] returns a list of terms [l], such that [t] is equal to
   the product of the elements of [l] by function [f].
   Function [sub_eq] is used to test equality between elements.
   [reduced] is set to true when [t] has really been simplified.
   [try_no_var] is as above. *)
val simp_prod : (term -> term) -> bool ref ->
  (term -> term -> bool) -> funsymb -> term -> term list

(* [make_prod prod l] computes the product by function [prod]
   of the elements in list [l]. [l] must not be empty. *)
val make_prod : funsymb -> term list -> term

(* [make_inv_prod eq_th l1 t l2] computes the product 
   inv (product (List.rev l1)) * t * inv(product l2) *)
val make_inv_prod : eq_th -> term list -> term -> term list -> term

(* [get_prod try_no_var t] returns the equational theory of the root
   function symbol of term [t], when it is a product
   in a group or xor. [try_no_var] is as in [compute_inv] above. *)
val get_prod : (term -> term) -> term -> eq_th
val get_prod_list : (term -> term) -> term list -> eq_th

(* [is_fun f t] is true if and only if the root function symbol
   of [t] is [f]. *)
val is_fun : funsymb -> term -> bool

(* [remove_inverse_ends try_no_var reduced group_th sub_eq l] removes the
   inverse elements at the two ends of the list [l]. In a non-commutative group,
   the product of the elements [l] is the neutral element if and only if the
   product of the resulting list is: x * t * x^-1 = e iff t = e by multiplying
   on the left by x^-1 and on the right by x. 
   [group_th = (f, inv,n)] is supposed to be a group, with product [f],
   inverse function [inv], and neutral element [n].    
   [try_no_var], [reduced], and [sub_eq] are as above. *)

val remove_inverse_ends :
  (term -> term) -> bool ref -> funsymb * funsymb * funsymb ->
  (term -> term -> bool) -> term list -> term list

(* [apply_eq_reds try_no_var reduced t] simplifies the term [t] using
   the equational theory. [reduced] is set when the term [t] is really
   simplified. [try_no_var] is as in [compute_inv] above. *) 
val apply_eq_reds : (term -> term) -> bool ref -> term -> term

(* Equality tests between terms, lists of terms, ... *)
val simp_equal_terms : (term -> term) -> term -> term -> bool
val equal_terms : term -> term -> bool
val synt_equal_terms : term -> term -> bool
val equal_term_lists : term list -> term list -> bool 
val equal_probaf : probaf -> probaf -> bool
val equal_def_lists : binderref list -> binderref list -> bool
val equal_elsefind_facts : elsefind_fact -> elsefind_fact -> bool

(* [is_subterm t1 t2] returns [true] when [t1] is a subterm of [t2]
   This function is allowed only for Var/FunApp/ReplIndex terms. *)
val is_subterm : term -> term -> bool

(* [len_common_suffix l1 l2] returns the length of the longest 
   common suffix between lists of terms [l1] and [l2] *)
val len_common_suffix : term list -> term list -> int

val equal_binderref : binderref -> binderref -> bool
val mem_binderref : binderref -> binderref list -> bool
val add_binderref : binderref -> binderref list ref -> unit
val setminus_binderref : binderref list -> binderref list -> binderref list
val inter_binderref : binderref list -> binderref list -> binderref list

val get_deflist_subterms : binderref list ref -> term -> unit
val get_deflist_process : binderref list ref -> inputprocess -> unit
val get_deflist_oprocess : binderref list ref -> process -> unit

val refers_to : binder -> term -> bool
val refers_to_br : binder -> binderref -> bool
val refers_to_pat : binder -> pattern -> bool
val refers_to_process : binder -> inputprocess -> bool
val refers_to_oprocess : binder -> process -> bool
val refers_to_fungroup :  binder -> fungroup -> bool

val refers_to_nodef : binder -> term -> bool
val refers_to_process_nodef : binder -> process -> bool

val vars_from_pat : binder list -> pattern -> binder list
val occurs_in_pat : binder -> pattern -> bool

val is_true : term -> bool
val is_false : term -> bool

val make_and_ext : Parsing_helper.extent -> term -> term -> term
val make_or_ext : Parsing_helper.extent -> term -> term -> term
val make_equal_ext : Parsing_helper.extent -> term -> term -> term
val make_diff_ext : Parsing_helper.extent -> term -> term -> term

val make_and : term -> term -> term
val make_or : term -> term -> term
val make_and_list : term list -> term
val make_or_list : term list -> term
val make_not : term -> term
val make_equal : term -> term -> term
val make_let_equal : term -> term -> term
val make_diff : term -> term -> term
val make_for_all_diff : term -> term -> term
val make_true : unit -> term
val make_false : unit -> term

val or_and_form : term -> term

val is_tuple : term -> bool
val is_pat_tuple : pattern -> bool

val put_lets : pattern list -> term list -> process -> process -> process
val put_lets_term : pattern list -> term list -> term -> term option -> term
exception Impossible
val split_term : funsymb -> term -> term list

val move_occ_term : term -> term
val move_occ_br : binderref -> binderref
(* [move_occ_process] renumbers the occurrences in the process given
   as argument. Additionally, it makes sure that all terms and processes
   inside the returned process are physically distinct, which is a 
   requirement for calling [Terms.build_def_process]. *)
val move_occ_process : inputprocess -> inputprocess

val term_from_pat : pattern -> term
val get_type_for_pattern : pattern -> typet

val count_var : term -> int
val size : term -> int

exception NonLinearPattern
val gvar_name : string
val gen_term_from_pat : pattern -> term
val single_occ_gvar : binder list ref -> term -> bool

val not_deflist : binder -> elsefind_fact -> bool
val not_deflist_l : binder list -> elsefind_fact -> bool

(* [close_def_subterm accu br] adds in [accu] all variable references in [br] *)
val close_def_subterm : binderref list ref -> binderref -> unit
(* [close_def_term accu t] adds in [accu] all variable references in [t] *)
val close_def_term : binderref list ref -> term -> unit
(* [defined_refs_find bl def_list defined_refs] computes a pair
   [(defined_refs_cond, defined_refs_branch)] of variable references
   guaranteed to be defined in the condition, resp. then branch of
   [find bl suchthat defined(def_list) && condition then branch], 
   assuming the variable references in [defined_refs] are already 
   known to be defined before the find. *)
val defined_refs_find : (binder * repl_index) list -> binderref list -> 
  binderref list -> binderref list * binderref list

(* [check_no_ifletfindres t] returns true if [t] is a basic term:
   it contains no if/let/find/new/event. *)
val check_no_ifletfindres : term -> bool

val def_term : (term * fact_info) list ref option -> def_node -> term list -> binderref list -> term -> def_node
val build_def_process : (term * fact_info) list ref option -> inputprocess -> unit
val add_def_vars_node : binder list -> def_node -> binder list

val cleanup_array_ref : unit -> unit
val array_ref_eqside : eqmember -> unit
val array_ref_process : inputprocess -> unit
val has_array_ref : binder -> bool
val has_array_ref_q : binder -> bool

val exclude_array_ref_term : binder list -> term -> unit
val exclude_array_ref_def_list : binder list -> binderref list -> unit
val exclude_array_ref_pattern : binder list -> pattern -> unit
val cleanup_exclude_array_ref : unit -> unit
val all_vars_exclude : binder list ref
val has_array_ref_non_exclude : binder -> bool

val unionq : 'a list -> 'a list -> 'a list (* union using physical equality *)

val compatible_empty : binderset
val empty_comp_process : inputprocess -> unit
val build_compatible_defs : inputprocess -> unit
val is_compatible : binderref -> binderref -> bool

(* Update args_at_creation: since variables in conditions of find have
as args_at_creation the indices of the find, transformations of the
find may lead to changes in these indices.  This function updates
these indices. It relies on the invariant that variables in conditions
of find have no array accesses, and that new/event do not occur in
conditions of find. It creates fresh variables for all variables
defined in the condition of the find. *)
val update_args_at_creation : repl_index list -> term -> term

(* Function to call by default in case of matching error *)

val default_match_error : unit -> 'a

(* [match_funapp match_term get_var_link match_error try_no_var next_f t t' state]
   matches [t] and [t']; [t] must be FunApp, otherwise matching
   is considered to fail. The other cases must have been handled previously.

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
   (In most cases, [match_error] should be [default_match_error],
   which raises the [NoMatch] exception.)

   [try_no_var]: [try_no_var t] tries to replace variables with their
   values in [t]; it returns the resulting term.

   [next_f]: [next_f state'] is called when the matching succeeds,
   that is, the variables in [t] are linked so that [\sigma t = t'].
   [next_f] can raise [NoMatch] to force the function to look for
   another matching.
*)

val match_funapp :
  (('b -> 'a) -> term -> term -> 'b -> 'a) ->
  (term -> 'b -> (linktype * bool) option) ->
  (unit -> 'a) -> 
  (term -> term) ->
  ('b -> 'a) -> term -> term -> 'b -> 'a

(* [match_assoc_subterm match_term get_var_link next_f try_no_var prod l1 l2 state]
   matches the lists of terms [l1] and [l2] modulo associativity of the product
   function [prod].
   More precisely, it calls [next_f left_rest right_rest state'] after linking variables in [l1]
   so that [left_rest. \sigma l1 . right_rest = l2] modulo associativity.
   [match_term], [get_var_link], [try_no_var] are as in the function
   [match_funapp] above.
   *)

val match_assoc_subterm :
  (('b -> 'a) -> term -> term -> 'b -> 'a) ->
  (term -> 'b -> (linktype * bool) option) ->
  (term list -> term list -> 'b -> 'a) ->
  (term -> term) ->
  funsymb -> term list -> term list -> 'b -> 'a

(* [match_AC match_term get_var_link match_error next_f try_no_var prod allow_rest l1 l2 state]
   matches the lists of terms [l1] and [l2] modulo associativity and commutativity
   of the product function [prod].
   [allow_rest] is true when one is allowed to match only a sublist of [l2] with [l1].
   When [allow_rest] is false, [match_AC] calls [next_f [] state'] after linking variables in [l1]
   so that [\sigma l1 = l2] modulo AC. 
   When [allow_rest] is true, it calls [next_f lrest state']  after linking variables in [l1]
   so that [\sigma l1 . lrest = l2] modulo AC. 

   [match_term], [get_var_link], [match_error], [try_no_var] are as in the function
   [match_funapp] above.
*)

val match_AC :
  (('b -> 'a) -> term -> term -> 'b -> 'a) ->
  (term -> 'b -> (linktype * bool) option) ->
  (unit -> 'a) -> 
  (term list -> 'b -> 'a) ->
  (term -> term) ->
  funsymb -> bool -> term list -> term list -> 'b -> 'a

(* [match_term_list match_term next_f l l' state] matches the lists of terms
   [l] and [l'], using [match_term] to match individual terms.
   [next_f state'] is called when the matching succeeds.
   It can raise [NoMatch] to force the function to look for
   another matching. *)

val match_term_list :
  (('b -> 'a) -> term -> term -> 'b -> 'a) ->
  ('b -> 'a) -> term list -> term list -> 'b -> 'a

(* Matching with advice, for use in transf_crypto.ml *)

(* [match_assoc_advice_subterm match_term explicit_value get_var_link is_var_inst next_f prod l1 l2 state]
   matches the lists [l1] and [l2] modulo associativity. 
   More precisely, it calls [next_f left_rest right_rest state']  after linking variables in [l1]
   so that [left_rest. \sigma l1 . right_rest = l2] modulo associativity.
   [left_rest] and [right_rest] may be empty. 

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

   [prod] is the product function symbol, which is associative or AC.
 *)

val match_assoc_advice_subterm :
  (('a -> 'b) -> term -> term -> 'a -> 'b) ->
  (term -> 'a -> 'a) ->
  (term -> 'a -> (linktype * bool) option) ->
  (term -> bool) ->
  (term list -> term list -> 'a -> 'b) ->
  funsymb -> term list -> term list -> 'a -> 'b

(* [match_assoc_advice_pat_subterm match_term explicit_value get_var_link is_var_inst next_f prod allow_full l1 l2 state]
   matches the lists [l1] and [l2] modulo associativity. 
   More precisely, it calls [next_f state']  after linking variables in [l1]
   so that [\sigma l1 = left_rest . l2 . right_rest] modulo associativity.
   [left_rest] and [right_rest] are just ignored, they are not passed to [next_f].

   [allow_full] is true when [l2] may match the full list [l1], that is,
   [left_rest] and [right_rest] may both be empty. 

   [match_term], [explicit_value], [get_var_link], [is_var_inst], [prod] 
   are as in the function [match_assoc_advice_subterm] above.   
 *)

val match_assoc_advice_pat_subterm :
  (('a -> 'b) -> term -> term -> 'a -> 'b) ->
  (term -> 'a -> 'a) ->
  (term -> 'a -> (linktype * bool) option) ->
  (term -> bool) ->
  ('a -> 'b) ->
  funsymb -> bool -> term list -> term list -> 'a -> 'b

(* [match_AC_advice match_term explicit_value get_var_link is_var_inst next_f prod allow_rest_pat allow_full allow_rest l1 l2 state]
   matches the lists [l1] and [l2] modulo AC. 
   When [allow_rest] and [allow_rest_pat] are false, it calls [next_f [] state'] after linking variables in [l1]
   so that [\sigma l1 = l2] modulo AC. 
   When [allow_rest] is true and [allow_rest_pat] is false, it calls [next_f lrest state']  after linking variables in [l1]
   so that [\sigma l1 . lrest = l2] modulo AC. 
   When [allow_rest] is false and [allow_rest_pat] is true, it calls [next_f [] state']  after linking variables in [l1]
   so that [\sigma l1 = l2 . lrest] modulo AC. [lrest] is ignored, it is not passed to [next_f].

   [allow_rest_pat] is true when a subterm of the pattern in [l1] should match
   [l2], so that some elements of [l1] are allowed to remain unmatched.

   In case [allow_rest_pat] is true, [allow_full] is true when [l2] may match the full list [l1], that is, [lrest] may be empty.

   [allow_rest] is true when the pattern in [l1] should match a subterm of 
   the term in [l2], so that some elements of [l2] are allowed to remain unmatched.

   [match_term], [explicit_value], [get_var_link], [is_var_inst], [prod] 
   are as in the function [match_assoc_advice_subterm] above.   
*)

val match_AC_advice :
  (('a -> 'b) -> term -> term -> 'a -> 'b) ->
  (term -> 'a -> 'a) ->
  (term -> 'a -> (linktype * bool) option) ->
  (term -> bool) ->
  (term list -> 'a -> 'b) ->
  funsymb -> bool -> bool -> bool -> term list -> term list -> 'a -> 'b

(* [match_funapp_advice match_term explicit_value get_var_link is_var_inst next_f t t' state]
   matches [t] with [t'] when they are function applications. More precisely,
   it calls [next_f state'] after linking variables in [t] such that [\sigma t = t'].

   [match_term], [explicit_value], [get_var_link], [is_var_inst]
   are as in the function [match_assoc_advice_subterm] above.   
 *)

val match_funapp_advice :
  (('a -> 'b) -> term -> term -> 'a -> 'b) ->
  (term -> 'a -> 'a) ->
  (term -> 'a -> (linktype * bool) option) ->
  (term -> bool) -> ('a -> 'b) -> term -> term -> 'a -> 'b

