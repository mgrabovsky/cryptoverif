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
(* Cryptographic functions *)

(* Public and secret RSA keys *)
type pkey
type skey

(* Serialization and deserialization functions for public and secret RSA keys *)
val pkey_from : string -> pkey
val pkey_to : pkey -> string
val skey_from : string -> skey
val skey_to : skey -> string

(* [injbot] is the injection from bitstring to bitstringbot (which maps [x] to [Some x]) 
   [injbot_inv] is the inverse function, which maps [Some x] to [x] and 
   raises [Base.Match_fail] when its argument is [None] *)
val injbot : string -> string option
val injbot_inv : string option -> string

(* Concatenation  and decomposition functions for pairs and triples of strings,
   and pairs public key, string *)
val concat_str_str : string -> string -> string
val unconcat_str_str : string -> (string * string)
val concat_str_str_str : string -> string -> string -> string
val unconcat_str_str_str : string -> (string * string * string)
val concat_pk_str : pkey -> string -> string
val unconcat_pk_str : string -> (pkey * string)

(* Returns the host name *)
val get_hostname : unit -> string

(*Padding*)
val pad : Cryptokit.Padding.scheme -> int -> string -> string
val pad_inv : Cryptokit.Padding.scheme -> string -> string

(*Symmetric encryption
  [sym_kgen]: key generation function, takes random coins and returns 
  the key (in fact, it is the identity) *)
val sym_kgen : string -> string
(* [sym_r_enc f] is the encryption function
   [sym_r_enc f msg key rd] returns the ciphertext, where 
   - [f] is a function that defines the encryption scheme. A recommended choice
   is Cryptokit.Cipher.aes ~mode:Cryptokit.Cipher.CBC ~pad:Cryptokit.Padding.length
   for AES in CBC mode with length padding.
   - [msg] is the cleartext
   - [key] is the encryption key. The appropriate length of the key is 
   determined by the underlying block cipher (16, 24, or 32 bytes for AES).
   - [rd] is a random initialization vector. Its length must be the block
   size of the underlying block cipher (16 bytes for AES). *)
val sym_r_enc : (?iv:string -> string -> Cryptokit.Cipher.direction -> Cryptokit.transform) -> string -> string -> string -> string
(* [sym_r_dec iv_size f] is the encryption function
   [sym_r_dec iv_size f msg key] returns (Some ciphertext) when decryption
   succeeds and (None) when decryption fails, where
   - [iv_size] is the size of the initialization vector, that is, the block size 
   of the underlying block cipher. It is determined by the underlying block cipher
   (16 for AES)
   - [f] is a function that defines the encryption scheme. A recommended choice
   is Cryptokit.Cipher.aes ~mode:Cryptokit.Cipher.CBC ~pad:Cryptokit.Padding.length
   for AES in CBC mode with length padding.
   - [msg] is the ciphertext
   - [key] is the encryption key. The appropriate length of the key is 
   determined by the underlying block cipher (16, 24, or 32 bytes for AES). *)
val sym_r_dec : int -> (?iv:string -> string -> Cryptokit.Cipher.direction -> Cryptokit.transform) -> string -> string -> string option

(* MAC
   [mac_kgen]: key generation function, takes random coins and returns 
   the key (in fact, it is the identity) *)
val mac_kgen : string -> string
(* [mac f] is the MAC function
   [mac f msg key] returns the MAC, where
   [f] is the underlying Cryptokit MAC function (e.g. Cryptokit.MAC.hmac_sha1 for HMAC SHA1)
   [msg] is the message to MAC
   [key] is the MAC key *)
val mac : (string -> Cryptokit.hash) -> string -> string -> string
(* [mac_check f] is the MAC verification function 
   [mac_check f msg key vmac] returns true when [vmac] is a correct mac of [msg] with key [key]
   It simply compares [vmac] with the MAC computed by [mac f msg key] *)
val mac_check : (string -> Cryptokit.hash) -> string -> string -> string -> bool

(* Public key cryptography *)

(* RSA key pair generation
   [pk_kgen size ()] returns a pair (RSA public key, RSA secret key),
   where [size] is the size of the modulus in bits (typically 1024 or 2048).
   This function is (obviously) probabilistic. An adequate model in CryptoVerif 
   can be defined using "letfun" as follows: 
      type keyseed [large,fixed].
      type pkey [bounded].
      type skey [bounded].
      type keypair [bounded].
      fun kp(pkey,skey):keypair [compos].
      letfun kgen() =  k <-R keyseed;  kp (pkgen(k) ,skgen(k) ).
      implementation 
        type pkey="pkey" [serial = "pkey_to","pkey_from"];
        type skey="skey" [serial = "skey_to","skey_from"];
        fun kp="id" [inverse="id"];
        fun kgen = "(pk_kgen 1024)".
   The function [kgen] has two definitions:
     - in the implementation, it uses [pk_kgen] (last line of the code above)
     - in the CryptoVerif game, it uses [k <-R keyseed; kp (pkgen(k), skgen(k))]
   ("letfun" line) which chooses random coins [k], and
   generates the key pair from these coins, so that the CryptoVerif
   key generation symbols [pkgen] and [skgen] are deterministic
   functions.  *) 
val pk_kgen : int -> unit -> (pkey * skey)

(* RSA-OAEP encryption scheme (using SHA-1 as a hash function)
   [pk_enc] is the encryption function, which takes as argument the
   cleartext and the public key, and returns the ciphertext. 
   [pk_enc] is a probabilistic function. An adequate model in CryptoVerif 
   can be defined using "letfun" as follows:
     expand IND_CCA2_public_key_enc(keyseed, pkey, skey, blocksize, bitstring, seed, skgen, pkgen, enc_r, dec, injbot, Z, Penc, Penccoll).
     letfun enc(msg: blocksize, k: pkey) = r <-R seed; enc_r(msg, k, r).
     implementation fun enc="pk_enc".
   The function [enc] has two definitions:
     - in the implementation, it uses [pk_enc]
     - in the CryptoVerif game, it uses [r <-R seed; enc_r(msg, k, r)]
   which chooses random coins and calls the encryption function [enc_r].
   [enc_r] itself is deterministic. *)
val pk_enc : string -> pkey -> string
(* [pk_dec] is the decryption function, which takes as argument the
   ciphertext and the secret key and returns [(Some cleartext)] if
   decryption succeeds and [None] if decryption fails. *)
val pk_dec : string -> skey -> string option


(* FDH (full domain hash) signature scheme
   [pk_sign h ps] is the signature function, which takes as argument
   the message to sign [msg] and the secret key [sk], and returns the signature.
   [h] is a hash function (e.g. Cryptokit.Hash.sha1 for SHA-1)
   [ps] is a padding scheme (e.g. Cryptokit.Padding.length) *)
val pk_sign : (unit -> Cryptokit.hash) -> Cryptokit.Padding.scheme -> string -> skey -> string
(* [pk_check_sign h ps] is the signature verification function, which
   takes as argument the signed message [msg], the public key [pk], and the 
   candidate signature [s], and returns true when [s] is a valid signature
   of [msg] under [pk]. 
   [h] and [ps] are as for [pk_sign]. *)
val pk_check_sign : (unit -> Cryptokit.hash) -> Cryptokit.Padding.scheme -> string -> pkey -> string -> bool


(* RSA-PSS signature scheme (using SHA-1 as a hash function)
   [rsassa_pss_sign sLen] is the signature function, which takes as argument
   the message to sign [msg] and the secret key [sk], and returns the 
   signature. 
   [sLen] is the length of the random coins in bytes.
   [rsassa_pss_sign sLen] is a probabilistic function. An adequate model in 
   CryptoVerif can be defined using "letfun" as follows:
      expand UF_CMA_signature(skeyseed, spkey, sskey, sblocksize, signature, sseed, sskgen, spkgen, sign_r, check, Psign, Psigncoll).
      letfun sign(msg: sblocksize, k: sskey) = r <-R sseed; sign_r(msg, k, r).
      implementation fun sign="(rsassa_pss_sign 8)".
   The function [sign] has two definitions:
     - in the implementation, it uses [rsassa_pss_sign]
     - in the CryptoVerif game, it uses [r <-R sseed; sign_r(msg, k, r)]
   which chooses random coins and calls the signature function [sign_r].
   [sign_r] itself is deterministic. 
*)
val rsassa_pss_sign : int -> string -> skey -> string
(* [rsassa_pss_verify sLen] is the signature verification function, which
   takes as argument the signed message [msg], the public key [pk], and the 
   candidate signature [s], and returns true when [s] is a valid signature
   of [msg] under [pk]. 
   [sLen] is the length of the random coins in bytes.
*)
val rsassa_pss_verify : int -> string -> pkey -> string -> bool

(*Diffie-Hellman *)

type dh_parameters
type dh_secret

(* The group 14 of rfc3526 *)
val dh_group14 : dh_parameters
(* Generates new parameters *)
val dh_new_parameters : ?rng:Cryptokit.Random.rng -> ?privlen:int -> int -> dh_parameters
(* [dh_rand params] Creates a new private secret using the parameters *)
val dh_rand : dh_parameters -> unit -> dh_secret
(* [dh_message params] calculates g^[x] mod p. Use with letfun message (x:Z) = exp(g,x) in CV source *)
val dh_message : dh_parameters -> dh_secret -> string
(* [dh_exp params] calculates [a]^[b] mod p and deletes the contents of b *)
val dh_exp : dh_parameters -> string -> dh_secret -> string

(* For debug purposes. Prints on stderr the time taken to compute the
   function in argument and returns its result. *)
val time : string -> (unit -> 'a) -> 'a
