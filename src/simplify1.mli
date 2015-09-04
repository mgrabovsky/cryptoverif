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

(* Helper functions for simplify, mergebranches, global_dep_anal, ... *)

(*** Computation of probabilities of collision between terms ***)

(* map_find_indices creates new replication indices, to replace find indices in
   probability computations.
   These indices are stored in repl_index_list. *)
val repl_index_list : (term * repl_index) list ref

val new_repl_index_term : term -> repl_index

(* Recorded term collisions *)
val term_collisions :
  ((binderref * binderref) list * (* For each br1, br2 in this list, the collisions are eliminated only when br2 is defined before br1 *)
   term * (* The collisions are eliminated only when this term is true *)
   term list * (* Facts that are known to hold when the collision is eliminated *)
   repl_index list * (* Indices that occur in colliding terms *) 
   repl_index list * (* Indices at the program point of the collision *)
   repl_index list * (* Reduced list of indices taking into account known facts *)
   term * term * (* The two colliding terms, t1 and t2 *)
   binder * term list option (* The random variable that is (partly) characterized by t1 and from which t2 is independent *) * 
   typet list (* The type(s) of the characterized part *)) list ref

(* Resets repl_index_list and term_collisions, and also calls Proba.reset *)
val reset : string list -> game -> unit

val any_term_pat : pattern -> term
val matches_pair : term -> term -> term -> term -> bool

(* Adds a term collision *)
val add_term_collisions :
  repl_index list * term list * (binderref * binderref) list * term -> term -> term ->
  binder -> term list option -> typet list -> bool

(* Computes the probability of term collisions *)
val final_add_proba : unit -> setf list

(*** Module used in dependency analyses ***)

module FindCompos :
  sig
    type status = Compos | Decompos | Any
(* The status is
   - [Compos] when a term [t] is obtained from a variable [b0] by first applying
     poly-injective functions (functions marked [compos]), then
     functions that extract a part of their argument 
     (functions marked [uniform]).
   - [Decompos] when [t] is obtained from [b0] by applying functions
     that extract a part of their argument (functions marked [uniform])
   - [Any] in the other cases *)

    type charac_type =
        CharacType of typet
      | CharacTypeOfVar of binder
    type 'a depinfo = (binder * (status * 'a)) list option * term list
      (* The dependency information has two components (dep, nodep):
	 If dep = Some l where l is a list of (variable, ...), such that it 
	 is guaranteed only variables in this list depend on the considered 
	 variable x[...].
	 If dep = None, we have no information of this kind; any variable 
	 may depend on x.
	 nodep is a list of terms that are guaranteed not to depend on x[l].
	 *)

    (* [init_elem] is the empty dependency information *)
    val init_elem : 'a depinfo

    (* [depends (b, depinfo) t] returns [true] when the term [t]
       may depend on the variable [b]. 
       [depinfo] is the dependency information for variable [b]. *)
    val depends : binder * 'a depinfo -> term -> bool

    (* [is_indep (b, depinfo) t] returns a term independent of [b]
       in which some array indices in [t] may have been replaced with
       fresh replication indices. When [t] depends on [b] by variables
       that are not array indices, it raises [Not_found] *)
    val is_indep : binder * 'a depinfo -> term -> term

    (* [remove_dep_array_index (b, depinfo) t] returns a modified 
       version of [t] in which the array indices that depend on [b]
       are replaced with fresh indices.
       [depinfo] is the dependency information for variable [b].*)
    val remove_dep_array_index : binder * 'a depinfo -> term -> term

    (* [remove_array_index t] returns a modified version of [t] in which
       the array indices that are not replication indices are replaced
       with fresh indices. *) 
    val remove_array_index : term -> term


    (* [find_compos check (b0, depinfo) ((b,(st,_)) as b_st) t] returns
       [Some(st', c, t')] when it could show that [t] characterizes a part of
       [b] (which itself characterizes a part of [b0]).
       [st'] is the status of [t] (Compos or Decompos; see above their meaning).
       [c] determines the type of the part of [b0] that [t] characterizes.
       [t'] is a modified version of [t] in which the parts that are not useful
       to show that [t] characterizes a part of [b] are replaced with variables [?].
       It returns [None] otherwise.

       [check] is a function that checks the validity of the indices of [b] inside [t]:
       [check b_st l] is called when [l] contains the array indices of [b] in [t];
       it returns [Some(st,c')] when these array indices are accepted; 
       [st] is the status of [b];
       [c'] determines the type of the part of [b0] that [b] characterizes.
       It returns [None] otherwise. *)
    val find_compos : (binder * (status * 'a) ->
       term list -> (status * charac_type) option) -> (binder * 'a depinfo) ->
      binder * (status * 'a) -> term -> (status * charac_type * term) option

    (* [find_compos_list] is the same as [find_compos] but for a list of variables
       instead of a single variable [((b,(st,_)) as b_st)]. 
       It tries each variable in turn until it finds one for which [find_compos]
       succeeds. *)
    val find_compos_list :
      (binder * (status * 'a) -> term list -> (status * charac_type) option) ->
      (binder * 'a depinfo) -> (binder * (status * 'a)) list -> term ->
      (status * charac_type * term * binder * 'a) option
  end

(*** Treatment of "elsefind" facts ***)

exception SuccessBranch of (binder * repl_index * term) list * (binder * repl_index) list
val branch_succeeds : 'b findbranch -> dep_anal -> simp_facts -> 
  binderref list -> unit
val add_elsefind : dep_anal -> binderref list -> simp_facts ->
  'a findbranch list -> simp_facts
val filter_elsefind : (elsefind_fact -> bool) -> simp_facts -> simp_facts
val convert_elsefind : dep_anal -> binderref list -> simp_facts -> simp_facts

(*** Evaluation of terms: 
     true_facts_from_simp_facts gets the true facts from a triple (facts, substitutions, else_find facts)
     try_no_var_rec replaces variables with their values as much as possible ***)

val true_facts_from_simp_facts : simp_facts -> term list

val try_no_var_rec : simp_facts -> term -> term

(* [get_facts_of_elsefind_facts] uses elsefind facts to derive more facts, 
   by performing a case distinction depending on the order of 
   definition of variables. 
   [get_facts_of_elsefind_facts g cur_array simp_facts def_vars]
   returns a list of terms [tl] that are proved.
   [g] is the current game
   [cur_array] the current replication indices
   [simp_facts] the facts known to hold at the current program point
   [def_vars] the variables known to be defined
   The probability that the facts do not hold must be collected from outside 
   [get_facts_of_elsefind_facts], by calling [Simplify1.reset] before
   and [Simplify1.final_add_proba()] after calling [get_facts_of_elsefind_facts].
*)

val get_facts_of_elsefind_facts : game -> repl_index list -> simp_facts -> binderref list -> term list

(*** Helper functions for cryptotransf: show that calls to oracles are incompatible or
   correspond to the same oracle call, to optimize the computation of probabilities. ***)

type compat_info_elem = term * term list * 
      repl_index list(* all indices *) * 
      repl_index list(* initial indices *) * 
      repl_index list(* used indices *) * 
      repl_index list(* really used indices *)

val filter_indices : term -> term list -> repl_index list -> term list -> 
  term list * compat_info_elem 
val is_compatible_indices : compat_info_elem -> compat_info_elem -> bool
val same_oracle_call : compat_info_elem -> compat_info_elem -> compat_info_elem option
