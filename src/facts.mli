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

(* 1. Compute and use simp_facts: facts that are separated into
   equalities that can be used as substitutions, other terms,
   else-find facts *)

(* Filter out terms if/let/find/res/event, so that the remaining terms
   can be used as facts *)
val filter_ifletfindres : term list -> term list

(* [try_no_var facts t] tries to transform [t] into a term that
   is not a variable, using the equalities in [facts] *)
val try_no_var : simp_facts -> term -> term

(* match_term is an intermediate function used for apply_reds. It is exported
   because we need to compute a variant of apply_reds in dependency analyses. *)
val match_term : (term -> term) -> binder list -> (unit -> 'a) -> term -> term -> unit -> 'a

(* set to true by the functions below when they reduce the term *)
val reduced : bool ref

(* [apply_eq_statements_and_collisions_subterms_once reduce_rec try_no_var t] 
   simplifies the term [t] using the equalities coming from the
   equational theories, the equality statements, and the collisions  
   given in the input file.
   [reduce_rec f t] must simplify the term [t] knowing the fact [f] 
   in addition to the already known facts. It sets the flag [reduced]
   when [t] has really been modified.
   [try_no_var t] must simplify the term [t] by replacing variables
   with their values according to currently known facts. *)
val apply_eq_statements_and_collisions_subterms_once : (term -> term -> term) -> (term -> term) -> term -> term

(* [apply_eq_statements_subterms_once try_no_var t] simplifies
   the term [t] using the equalities coming from the
   equational theories and the equality statements given in the input file.
   [try_no_var] is as above. *)
val apply_eq_statements_subterms_once : (term -> term) -> term -> term

(* [apply_reds simp_facts t] applies all equalities coming from the
   equational theories, equality statements, and collisions given in
   the input file to all subterms of the term [t], taking into account
   the equalities in [simp_facts] to enable their application.
   Application is repeated until a fixpoint is reached. *)
val apply_reds : simp_facts -> term -> term

(* Display the facts. Mainly used for debugging *)
val display_facts : simp_facts -> unit

(* A dependency analysis is a function of type 
   [dep_anal = simp_facts -> term -> term -> bool] 
   such that [dep_anal facts t1 t2] is true when [t1 != t2] 
   up to negligible probability, by eliminating collisions
   between [t1] and [t2] using the results of some dependency analysis.

   [no_dependency_anal] is a particular dependency analysis that
   does nothing, i.e. always returns false.
   Other dependency analyses are defined in simplify.ml.
 *)
val no_dependency_anal : dep_anal

(* [simplif_add dep_anal facts t] updates the facts by taking into
   account that the term [t] is true. It can use [dep_anal] to eliminate
   collisions. 
   Raises Contradiction when the added fact [t] cannot be true when
   [facts] hold.
*)
val simplif_add : dep_anal -> simp_facts -> term -> simp_facts
(* [simplif_add_find_cond] is the same as [simplif_add] except
   that it allows (and ignores) terms that are not variables or function
   applications *)
val simplif_add_find_cond : dep_anal -> simp_facts -> term -> simp_facts
(* [simplif_add_list dep_anal facts tl] updates the facts by taking into
   account that the terms in [tl] are true. It can use [dep_anal] to eliminate
   collisions.
   Raises Contradiction when the added facts [tl] cannot be true when
   [facts] hold.
 *)
val simplif_add_list : dep_anal -> simp_facts -> term list -> simp_facts

(* 2. Compute the facts that hold and the variables that are defined
   at certain program points. *)

(* [get_node fact_info] gets the node from the p_facts field of a 
   process / the t_facts field of a term *)
val get_node : fact_info -> def_node option

(* [def_vars_from_defined current_node def_list] returns the variables that
   are known to be defined when the condition of a find with defined condition 
   [def_list] holds. [current_node] is the node of the find, at which [def_list]
   is tested (may be returned by [get_node]).
   Raises Contradiction when a variable that must be defined when [def_list]
   is defined has no definition in the game. *)
val def_vars_from_defined : def_node option -> binderref list -> binderref list

(* [facts_from_defined current_node def_list] returns the facts that
   are known to hold when the condition of a find with defined condition 
   [def_list] holds. [current_node] is the node of the find, at which [def_list]
   is tested (may be returned by [get_node]).
   Raises Contradiction when a variable that must be defined when [def_list]
   is defined has no definition in the game. *)
val facts_from_defined : def_node option -> binderref list -> term list

(* Returns fresh array indices for the variable given as argument *)
val make_indexes : binder -> term list

(* [get_def_vars_at fact_info] returns the variables that are known
   to be defined given [fact_info].
   May raise Contradiction when the program point at [fact_info] is
   unreachable. *)
val get_def_vars_at : fact_info -> binderref list

(* [get_facts_at fact_info] returns the facts that are known to hold
   given [fact_info].
   May raise Contradiction when the program point at [fact_info] is
   unreachable. *)
val get_facts_at : fact_info -> term list

(* [reduced_def_list fact_info def_list] removes variables that are 
   certainly defined from a [def_list] in a find. [fact_info] corresponds
   to the facts at the considered find. *)
val reduced_def_list : fact_info -> binderref list -> binderref list

(* Functions useful to simplify def_list *)
val filter_def_list : binderref list -> binderref list -> binderref list
val remove_subterms : binderref list -> binderref list -> binderref list
val eq_deflists : binderref list -> binderref list -> bool

(* 3. Some rich functions that rely on collecting facts and reasoning 
   about them *)

(* [check_distinct b g] show that elements of the array [b] 
   at different indices are always different (up to negligible probability).
   This is useful for showing secrecy of a key, and is called from success.ml.
   [g] is the full game. In addition to the boolean result, when it is true, 
   it also returns the probability of collisions eliminated to reach that 
   result.
*)
val check_distinct : binder -> game -> bool * setf list

(* [check_corresp corresp internal_info g] returns true when the
   correspondence [corresp] is proved (up to negligible probability).
   It is called from success.ml. [g] is the full game. In addition to the
   boolean result, when it is true, it also returns the probability of
   collisions eliminated to reach that result. *)
val check_corresp : (bool * term) list * qterm -> game -> bool * setf list

(* [simplify_term dep_anal facts t] returns a simplified form of
   the term [t] using the dependency analysis [dep_anal] and the
   true facts [facts]. *)
val simplify_term : dep_anal -> simp_facts -> term -> term

(* [check_equal g t t' facts] returns true when [t] and [t'] are
   proved equal when the terms in [facts] are true (up to negligible
   probability. It is called from insertinstruct.ml. [g] is the full
   game.  [t] is supposed to be a term of the game [g], [t'] is a
   candidate replacement for [t]. In addition to the boolean result,
   when it is true, it also returns the probability of collisions
   eliminated to reach that result and the updated eliminated
   collisions.  Terms.build_def_process must have been called so that
   t.t_facts has been filled. *)
val check_equal : game -> term -> term -> term list -> setf list -> bool * setf list

(* [is_reachable n n'] returns true when [n] is reachable from [n'],
   that is, the variable defined at [n] is defined above than the one 
   defined at [n']. *)
val is_reachable : def_node -> def_node -> bool


val display_facts_at : inputprocess -> int -> unit
