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
(* Exception Bad_call is raised when one tries to call several times
   an oracle that can be called only once, or one calls an oracle
   with data that are not of the right types. *)
exception Bad_call

(* Exception Match_fail is raised when a pattern-matching fails
   or one executes "yield" (channel front-end) / "end" 
   (oracles front-end) *)
exception Match_fail

(* Exception Abort is raised when executing "abort".
   The system should stop whole the protocol *) 
exception Abort

(* Exception Bad_file is raised when reading/writing a file leads to an
   error. The argument is the name of the file. *)
exception Bad_file of string

(* Reading from and writing to a file *)

val input_string_from_file : string -> string
val output_string_to_file : string -> string -> unit

(* [exc_bad_file fname f v] calls [f v]; if it raises [Match_fail], 
   raises [Bad_file fname] instead. This function is useful because
   when deserialization fails, it raises [Match_fail]. When we use
   deserialization for reading a file, we want to raise [Bad_file]
   instead. *)

val exc_bad_file : string -> ('a -> 'b) -> 'a -> 'b

(* Random number generation. *)

val rng : unit -> Cryptokit.Random.rng

val rand_string : int -> unit -> string
val rand_bool : unit -> bool
(* [rand_list l] returns a random element of [l].
   It is used for implementing "get": when several elements satisfy
   the desired condition, one of them is chosen randomly. *)
val rand_list : 'a list -> 'a

(* [char4_of_int s pos val] writes the integer [val] at position
   [pos] in the string [s]. The integer takes 4 bytes. 
   [int_of_char4 s pos] reads the integer at position [pos]
   in the string [s]. *)
val char4_of_int : string -> int -> int -> unit
val int_of_char4 : string -> int -> int

(* [compos] concatenates bitstrings, with length indications,
   so that the initial bitstrings can be recovered. 
   [decompos] recovers the initial bitstrings. 
   These functions are used for building and breaking tuples. 
   When [decompos] fails, raises [Match_fail] *)

val compos : string list -> string
val decompos : string -> string list

(* Read from and write to a table
   [get_from_table] is used for implementing "get"
   [insert_in_table] is used for implementing "insert"

   [get_from_table file filter] reads the table in file [file]
   and returns the image of entries by [filter]. Entries
   [e] such that [filter e] raises [Match_fail] are removed. *)

val get_from_table : string -> (string list -> 'a) -> 'a list
val insert_in_table : string -> string list -> unit

(* Predicates, to test whether a value belongs to a type.
   * [always_true] is always true; this predicate can be used
   for types such that the Caml representation always 
   corresponds to a valid CryptoVerif value 
   * [sizep n] is true for strings of [n] bits ([n] multiple of 8).
   It is used for fixed-length types. *)

val always_true : 'a -> bool
val sizep : int -> string -> bool

(* Serialization and deserialization functions for the default types:
   bitstring, bool, bitstrings having a fixed size, bitstringbot
   When deserialization fails, raises Match_fail *)

val id : 'a -> 'a
val bool_from : string -> bool
val bool_to : bool -> string
val size_from : int -> string -> string
val stringbot_from : string -> string option
val stringbot_to : string option -> string



(* Utilities *)

(* [ceildiv] is the function that returns the lowest integer that is
   greater or equal to [n]/[d]. [n] and [d] must be positive or equal
   to zero *)
val ceildiv : int -> int -> int

(* [i2osp] is the function that returns the representation of the number 
   [x] in a string of size [l]. *)
val i2osp : int -> int -> string
val osp2i : string -> int -> int -> int
