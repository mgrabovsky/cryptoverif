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

(* Helper functions for simplify, mergebranches, global_dep_anal, ... *)

(*** Computation of probabilities of collision between terms ***)

(* map_find_indices creates new replication indices, to replace find indices in
   probability computations.
   These indices are stored in repl_index_list. *)
val repl_index_list : (term * repl_index) list ref

(* Recorded term collisions *)
val term_collisions :
  ((binderref * binderref) list * (* For each br1, br2 in this list, the collisions are eliminated only when br2 is defined before br1 *)
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
  repl_index list * term list * (binderref * binderref) list -> term -> term ->
  binder -> term list option -> typet list -> bool

(* Computes the probability of term collisions *)
val final_add_proba : unit -> setf list

(*** Module used in dependency analyses ***)

module FindCompos :
  sig
    type status = Compos | Decompos | Any
    type charac_type =
        CharacType of typet
      | CharacTypeOfVar of binder
    type 'a depinfo = (binder * (status * 'a)) list option * term list
    val init_elem : 'a depinfo
    val depends : binder * 'a depinfo -> term -> bool
    val is_indep : binder * 'a depinfo -> term -> term
    val remove_dep_array_index : binder * 'a depinfo -> term -> term
    val remove_array_index : term -> term
    val find_compos : (binder * (status * 'a) ->
       term list -> (status * charac_type) option) -> 'a depinfo ->
      binder * (status * 'a) -> term -> (status * charac_type * term) option
    val find_compos_list :
      (binder * (status * 'a) -> term list -> (status * charac_type) option) ->
      'a depinfo -> (binder * (status * 'a)) list -> term ->
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
   [get_facts_of_elsefind_facts g cur_array return_proba simp_facts def_vars find_branch]
   returns a pair [(tl, proba)] of terms [tl] that are proved, with
   the negligible probability [proba] that they do not hold.
   [g] is the current game
   [cur_array] the current replication indices
   [return_proba] is true when the probability that the facts do not hold should be returned,
   and false when this probability is collected from outside [get_facts_of_elsefind_facts].
   (In this case, the returned [proba] is the empty list.)
   [simp_facts] the facts known to hold at the current program point
   [def_vars] the variables defined before the current find
   [def_list] the defined condition of a branch of find such that the returned fact hold
   inside that branch.
*)

val get_facts_of_elsefind_facts : game -> repl_index list -> bool -> simp_facts -> binderref list -> binderref list -> term list * setf list

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
