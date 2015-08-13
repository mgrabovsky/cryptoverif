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

type pkey
type skey

(* Tags *)

val tag_disconnect                : char
val tag_ignore                    : char
val tag_unimplemented             : char
val tag_debug                     : char
val tag_service_request           : char
val tag_service_accept            : char
val tag_kex_init                  : char
val tag_newkeys                   : char
val tag_kexdh_init                : char
val tag_kexdh_reply               : char
val tag_userauth_request          : char
val tag_userauth_failure          : char
val tag_userauth_success          : char
val tag_userauth_banner           : char
val tag_userauth_pk_ok            : char
val tag_global_request            : char
val tag_request_success           : char
val tag_request_failure           : char
val tag_channel_open              : char
val tag_channel_open_confirmation : char
val tag_channel_open_failure      : char
val tag_channel_window_adjust     : char
val tag_channel_data              : char
val tag_channel_extended_data     : char
val tag_channel_eof               : char
val tag_channel_close             : char
val tag_channel_request           : char
val tag_channel_success           : char
val tag_channel_failure           : char



(* Functions to get public and private ssh-rsa keys*)
val pkey_to : pkey -> string
val skey_to : skey -> string
val pkey_from : string -> pkey
val skey_from : string -> skey
val pkey_to_file : pkey -> string
val pkey_from_file : string -> pkey

val kgen : ?e:int -> int -> unit -> (pkey * skey)

(* Function to create a packet from a payload *)
val ssh_pad : int (* block size *) -> string -> string
val ssh_unpad : string -> string option

(*concatenates tag and payload for the tag*)
val concatm : char -> string -> string
val unconcatm : string -> char * string

(* utilities *)
val ssh_string : string -> string
val strings_of_ssh_string_ind : string -> int -> int -> string list 
val signature_from_ind : string -> int -> string
val skey_to_pkey : skey -> pkey

(*concatenates the values for the negotiation*)
val negotiation_string : string
val concatn : string -> string -> string
val unconcatn : string -> (string * string)
val check_algorithms : string -> bool

(*concatenates both parts of a message *)
val concatmsm : string -> string -> string

(* hash function : sha1 *)
val hash : unit -> string -> string

val g_of_mpint : string -> string
val mpint_of_g : string -> string

val signature_to : string -> string
val signature_from : string -> string

(* concatenation for KEXDH_REPLY (pk,g,sig) *)
val concat3 : pkey -> string -> string -> string
val unconcat3 : string -> (pkey * string * string)

(* concatenation to get the value to hash to get the shared hash *)
val concat8 : string -> string -> string -> string -> pkey -> string ->  string -> string -> string


val sign : string -> skey -> string
val check : string -> pkey -> string -> bool

(* creation of IV, symmetric keys, mac keys from shared secrets *)
val construct : int -> string -> unit -> string -> string -> string -> string

(* symmetric encryption/decryption, with IV *)
val symenc : string -> string -> string -> string
val symdec : string -> string -> string -> string option

val mac : string -> string -> string
val check_mac : string -> string -> string -> bool

(* concatenation of the message number and the payload *)
val concatnm : int -> string -> string

(* get the size of the packet from the first block *)
val get_size : string -> int

(* concatenation of the encrypted message and the MAC *)
val concatem : string -> string -> string

(* ssh-userauth string *)
val ssh_userauth : string
(* ssh-connection string *)
val ssh_connection : string
