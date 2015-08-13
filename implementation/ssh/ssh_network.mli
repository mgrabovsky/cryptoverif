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

val resolve : string -> Unix.inet_addr
val input_packet : in_channel -> string
val output_packet : out_channel -> string -> unit
val chop : string -> string
val input_blocks : in_channel -> int -> string
val input_block : in_channel -> string
val input_mac : in_channel -> string
(* this function takes as input the input and output channel, the closure corresponding to the initialization of the tunnel, and returns two functions, read and write *)
val create_tunnel : (in_channel * out_channel) -> (unit -> ((string * string * int -> unit * string) * (string * string -> (string * string * string * int -> unit * string) * int)) * string * string * string) -> (unit -> string) * (string -> unit) * string
val string_of_char : char -> string

(*message parsing*)
val parse_message_tag : string -> int -> char * int
val parse_int : string -> int -> int * int
val parse_string : string -> int -> string * int
val parse_bool : string -> int -> bool * int

