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

module StringMap : Map.S with type key = string ;;
module BinderSet : Set.S with type elt = string ;;

val info : string -> unit
val error : string -> 'a

val string_list_sep : string -> string list -> string
val string_list_sep_ignore_empty : string -> string list -> string

val is_alphabetic : char -> bool
val hex_of_char : char -> string
val alphabetize_string : string -> string

val get_oracle_name : string -> string
val get_binder_name : binder -> string
val get_binderref_name : Parsing_helper.extent -> binder * term list -> string

val iprocess_get_vars : inputprocess -> BinderSet.t * BinderSet.t * BinderSet.t
val oprocess_get_vars : process -> BinderSet.t * BinderSet.t * BinderSet.t

val impl_check : impl_process list -> impl_process list

val create_fresh_name : string -> string
val create_fresh_names : string -> int -> string list

val check_oracle_compatibility : string -> typet list * (bool * string) list -> typet list * (bool * string) list -> unit
val check_argument_type_compatibility : string -> typet list -> typet list -> unit

val term_tuple_types : term -> typet list
val pat_tuple_types : pattern -> typet list

val get_type_name : typet -> string
val get_type_predicate : typet -> string
val get_table_file : table -> string
val get_read_serial : typet -> string
val get_write_serial : typet -> string

