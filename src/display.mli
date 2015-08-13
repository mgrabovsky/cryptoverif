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

val display_occurrences : bool ref
val display_arrays : bool ref
val display_list : ('a -> unit) -> 'a list -> unit

val len_num : int -> int
val useful_occs : int list ref
val mark_occs : detailed_instruct list -> unit

val ends_with_underscore_number : string -> bool
val binder_to_string : binder -> string
val repl_index_to_string : repl_index -> string
val display_binder : binder -> unit
val display_repl_index : repl_index -> unit
val display_var : binder -> term list -> unit
val display_term : term -> unit
val display_statement : statement -> unit
val display_pattern : pattern -> unit
val display_proba : int -> probaf -> unit
val display_set : setf list -> unit
val display_equiv : equiv_nm -> unit
val display_equiv_with_name : equiv_nm -> unit
val display_oprocess : string -> process -> unit
val display_process : inputprocess -> unit

val display_bl_assoc : binder list -> unit
val display_query : query * game -> unit
val display_instruct : instruct -> unit

(* The next functions are made public so that displaytex can call them *)

type query_specif =
    InitQuery of query
  | QEvent of funsymb

val equal_qs : query_specif * game -> query_specif * game -> bool

type proof_tree =
    { pt_game : game;
      mutable pt_sons : (instruct * setf list * proof_tree * (query_specif * game) list ref) list }

exception NotBoundEvent of funsymb * game

val build_proof_tree : query * game -> setf list -> state -> proof_tree

val double_if_needed : (query_specif * game) list -> setf list -> setf list

(* [proba_from_set q p] converts the probability [p] represented as
a [setf list] into a probability represented as a [probaf].
[p] must not contain [SetEvent]. *)

val proba_from_set : setf list -> probaf
val proba_from_set_may_double : query * game -> setf list -> probaf


val get_initial_queries : state -> ((query * game) * proof_t ref * proof_t) list

val get_all_states_from_queries : ((query * game) * proof_t ref * proof_t) list -> state list

val remove_duplicate_states : state list -> state list -> state list


val display_state : state -> unit

