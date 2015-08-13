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
exception PKU_Error (* error while unwrapping a signature *)
exception Message_too_long (* Message given to a RSA primitive longer than k.size/8-1 bytes*)
exception Encoding_error
exception Decoding_error
exception Mask_too_long
exception Sxor

(* Types for public key crypto *)
type pkey = 
    { 
      psize : int;
      pn : string;
      pe : string;
    }
type skey = Cryptokit.RSA.key

let time msg f =
  let t1 = Sys.time () in
  let result = f () in
  let t2 = Sys.time () in
  Printf.eprintf "Time elapsed (%s): %f" msg (t2 -. t1);
  result

let pkey_from s =
  let (pk:pkey) = Marshal.from_string s 0 in
    pk

let pkey_to p =
  Marshal.to_string p [] 


let skey_from s =
  let (sk:skey) = Marshal.from_string s 0 in
    sk

let skey_to s =
  Marshal.to_string s [] 

(* Non cryptographic functions *)

let injbot_inv= function
    None -> raise Base.Match_fail
  | Some x-> x

let injbot x = Some x

let concat_str_str a b = Base.compos [a;b]
let unconcat_str_str x = 
  try 
    match (Base.decompos x) with 
        [a;b] -> (a,b) 
      | _ -> raise Base.Match_fail
  with 
      _ -> raise Base.Match_fail

let concat_str_str_str a b c = Base.compos [a;b;c]
let unconcat_str_str_str x = 
  try 
    match (Base.decompos x) with 
        [a;b;c] -> (a,b,c) 
      | _ -> raise Base.Match_fail
  with 
      _ -> raise Base.Match_fail

let concat_pk_str a b = Base.compos [(pkey_to a);b]
let unconcat_pk_str x = 
  try 
    match (Base.decompos x) with 
        [a;b] -> ((pkey_from a),b) 
      | _ -> raise Base.Match_fail
  with
      _ -> raise Base.Match_fail

let get_hostname = Unix.gethostname

(* Padding functions *)

let pad scheme size s =
  let buf = String.create size in
  let size=String.length s in
    String.blit s 0 buf 0 size;
    Cryptokit.wipe_string s;
    scheme#pad buf size;
    buf

let pad_inv scheme s =
  String.sub s 0 (scheme#strip s)


(* Symmetric encryption *)

let sym_kgen b = 
  b

(*f should be of the form, for example,
  Cryptokit.Cipher.aes ~mode:Cryptokit.Cipher.CBC ~pad:Cryptokit.Padding.length
  for an AES CBC padded with length padding scheme *)
let sym_enc f msg key =
  let t=f key Cryptokit.Cipher.Encrypt in
    t#put_string msg;
    t#finish;
    let s=t#get_string in
      t#wipe;
      s

let sym_dec f msg key =
  try 
    let t=f key Cryptokit.Cipher.Decrypt in
      t#put_string msg;
      t#finish;
      let s=t#get_string in
        t#wipe;
        Some s
  with
      _ -> None

let sym_r_enc f msg key rd =
  rd^(sym_enc (f ?iv:(Some rd)) msg key)

(* Two choices; change the interface to add iv_size here, or use C.Block.block_cipher (and create new functions for stream_cipher) *)
let sym_r_dec iv_size f msg key =
  let rd = String.sub msg 0 iv_size in
  let m = String.sub msg iv_size ((String.length msg) - iv_size) in
    sym_dec (f ?iv:(Some rd)) m key
        
(* MAC handling *)

let mac_kgen k=
  k

(*f should be of the form, for example,
  Cryptokit.MAC.hmac_sha1
  for a MAC based on SHA1 *)
let mac f msg key =
  let h=f key in
  Cryptokit.hash_string h msg

let mac_check f msg key mac =
  let h=f key in
  (mac = Cryptokit.hash_string h msg)


(* Public key crypto : RSA *)

let key_to_pkey k = 
  {psize = k.Cryptokit.RSA.size; 
   pn = k.Cryptokit.RSA.n; 
   pe = k.Cryptokit.RSA.e}

let pkey_to_key pk = 
  { Cryptokit.RSA.size = pk.psize; 
    Cryptokit.RSA.n = pk.pn; 
    Cryptokit.RSA.e = pk.pe;
    Cryptokit.RSA.d = "";
    Cryptokit.RSA.p = "";
    Cryptokit.RSA.q = "";
    Cryptokit.RSA.dp = "";
    Cryptokit.RSA.dq = "";
    Cryptokit.RSA.qinv = ""}

let pk_kgen size () =
  let k = Cryptokit.RSA.new_key ~rng: (Base.rng()) size in
    (key_to_pkey k, k)

(* RSA-OEAP encryption scheme *)

let mgf z l =
  let hLen = 20 in
  if (Sys.word_size > 32) then
    if l > hLen * (1 lsl 32) then
      raise Mask_too_long;
  let t = Buffer.create 80 in
  let m = (Base.ceildiv l hLen) - 1 in
    for counter = 0 to m do
      let c = Base.i2osp counter 4 in
        Buffer.add_string t (Cryptokit.hash_string (Cryptokit.Hash.sha1 ()) (z^c));
    done;
    Buffer.sub t 0 l
          
        
let sxor s1 s2 =
  if String.length s1 <> String.length s2 then
    raise Sxor
  else
    let s=String.create (String.length s1) in
      for i = 0 to ((String.length s1)-1) do
        s.[i] <- char_of_int ((int_of_char s1.[i]) lxor (int_of_char s2.[i]))
      done;
      s

let eme_oaep_encode m p emLen =
  (*step1 :P<=2**61-1. OCaml strings can have at most 2**57 octets *)
  let hLen = 20 in (*sha1 output size*)
    if (String.length m > emLen - 2* hLen -1) then
      raise Message_too_long
    else
      let ps = String.make (emLen - (String.length m) - 2*hLen -1) '\000' in
      let pHash = Cryptokit.hash_string (Cryptokit.Hash.sha1 ()) p in
      let db = pHash^ps^"\001"^m in
      let seed = Base.rand_string hLen () in
      let dbMask = mgf seed (emLen-hLen) in
      let maskedDB = sxor db dbMask in
      let seedMask = mgf maskedDB hLen in
      let maskedSeed = sxor seed seedMask in
        maskedSeed^maskedDB 


let eme_oaep_decode em p =
  let hLen = 20 in
    if String.length em < 2*hLen +1 then
      raise Decoding_error
    else
      let maskedSeed = String.sub em 0 hLen in
      let maskedDB = String.sub em hLen ((String.length em)-hLen) in
      let seedMask = mgf maskedDB hLen in
      let seed = sxor maskedSeed seedMask in
      let dbMask = mgf seed ((String.length em) - hLen) in
      let db = sxor maskedDB dbMask in
      let pHash =  Cryptokit.hash_string (Cryptokit.Hash.sha1 ()) p in
      let pHash' = String.sub db 0 hLen in
      let i = ref hLen in
      let dbl = String.length db in
      while !i < dbl && db.[!i] = '\000' do incr i done;
        if !i = dbl then raise Decoding_error
        else if db.[!i] <> '\001' then raise Decoding_error
        else if pHash <> pHash' then raise Decoding_error 
        else
          let i' = !i+1 in
          let m = String.sub db i' (dbl - i') in
            m

let rsaes_oaep_encrypt msg pk p =
  let k = Base.ceildiv pk.psize 8 in
  let em = eme_oaep_encode msg p (k-1) in
    Cryptokit.RSA.encrypt (pkey_to_key pk) em
      
let rsaes_oaep_decrypt msg sk p =
  try 
    let k = Base.ceildiv sk.Cryptokit.RSA.size 8 in
      if String.length msg <> k then
        None
      else
        let m=Cryptokit.RSA.decrypt_CRT sk msg in
          if m.[0] <> '\000' then
            None
          else
            let em = String.sub m 1 ((String.length m)-1) in
            Some (eme_oaep_decode em p)
  with 
      _ -> None


let pk_enc msg pk =
  rsaes_oaep_encrypt msg pk ""

let pk_dec msg sk = 
  rsaes_oaep_decrypt msg sk ""

(* Full domain hash (FDH) signature scheme *)

let pk_sign h ps msg sk = 
  let size = (Base.ceildiv sk.Cryptokit.RSA.size 8)-1 in
  let msg' = pad ps size (Cryptokit.hash_string (h ()) msg) in
    Cryptokit.RSA.sign_CRT sk msg'

let pk_unwrap ps s pk =
  let mp=Cryptokit.RSA.unwrap_signature (pkey_to_key pk) s in
    if mp.[0] <> '\000' then
      raise PKU_Error
    else
      pad_inv ps (String.sub mp 1 ((String.length mp)-1))

let pk_check_sign h ps msg pk s = 
  try
    let msg' = Cryptokit.hash_string (h ()) msg in
      pk_unwrap ps s pk = msg'
  with
      _ -> false

(* PSS signature scheme *)

let set_leftmost_n_bits_to_zero c n =
  let x = int_of_char c in
  let mask = (1 lsl(8-n))-1 in (* = 0..01..1 with n 0 and (8-n) 1 *)
    char_of_int (x land mask)

(* 8hLen + 8sLen + 9 <= emBits *)
let emsa_pss_encode sLen msg emBits =
  let hLen = 20 in (*sha1 output size*) 
  let emLen = Base.ceildiv emBits 8 in
  let mHash = Cryptokit.hash_string (Cryptokit.Hash.sha1 ()) msg in
    if emLen < hLen + sLen +2 then
      raise Encoding_error
    else
      let salt = Base.rand_string sLen () in
      let m' = "\000\000\000\000\000\000\000\000"^mHash^salt in
      let h = Cryptokit.hash_string (Cryptokit.Hash.sha1 ()) m' in
      let ps = String.make (emLen - sLen - hLen - 2) '\000' in
      let db = ps^"\001"^salt in
      let dbMask = mgf h (emLen - hLen -1) in
      let maskedDB = sxor db dbMask in
        maskedDB.[0] <- set_leftmost_n_bits_to_zero maskedDB.[0] (8*emLen-emBits);
        maskedDB^h^"\xbc"

let emsa_pss_verify sLen m em emBits =
  let hLen = 20 in
  let emLen = Base.ceildiv emBits 8 in
    if String.length em <> emLen then
      false
    else
      let mHash =  Cryptokit.hash_string (Cryptokit.Hash.sha1 ()) m in
        if emLen < hLen + sLen + 2 then false
        else
          if em.[emLen - 1] <> '\xbc' then
            false
          else
            let maskedDB = String.sub em 0 (emLen - hLen - 1) in
            let h = String.sub em (emLen - hLen - 1) hLen in
              if set_leftmost_n_bits_to_zero maskedDB.[0] (8*emLen-emBits) <> maskedDB.[0] then
                false
              else
                let dbMask = mgf h (emLen - hLen - 1) in
                let db = sxor maskedDB dbMask in
                  db.[0] <- set_leftmost_n_bits_to_zero db.[0] (8*emLen-emBits);
                  let i = ref 0 in
                  let b = ref true in
                    while !b && !i < emLen - hLen - sLen - 2 do
                      b := db.[!i] = '\000';
                      incr i;
                    done;
                    if not !b then
                      false
                    else
                      let salt = String.sub db (String.length db - sLen) sLen in
                      let m' = "\000\000\000\000\000\000\000\000"^mHash^salt in
                      let h' = Cryptokit.hash_string (Cryptokit.Hash.sha1 ()) m' in
                        h = h'

let rsassa_pss_sign sLen m sk =
  let em = emsa_pss_encode sLen m (sk.Cryptokit.RSA.size - 1) in
  let s = Cryptokit.RSA.sign_CRT sk em in
    s

let rsassa_pss_verify sLen m pk s =
  let k = Base.ceildiv pk.psize 8 in
  if (String.length s) <> k then 
    false
  else
    try 
      let em = Cryptokit.RSA.unwrap_signature (pkey_to_key pk) s in
        emsa_pss_verify sLen m em (pk.psize - 1)
    with 
        _ -> false


(* Diffie-Hellman *)

type dh_parameters = Cryptokit.DH.parameters
type dh_secret = Cryptokit.DH.private_secret

let dh_new_parameters = Cryptokit.DH.new_parameters

let dh_group14 = 
  { Cryptokit.DH.p = 
      "\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xC9\x0F\xDA\xA2\x21\x68\xC2\x34\xC4\xC6\x62\x8B\x80\xDC\x1C\xD1\x29\x02\x4E\x08\x8A\x67\xCC\x74\x02\x0B\xBE\xA6\x3B\x13\x9B\x22\x51\x4A\x08\x79\x8E\x34\x04\xDD\xEF\x95\x19\xB3\xCD\x3A\x43\x1B\x30\x2B\x0A\x6D\xF2\x5F\x14\x37\x4F\xE1\x35\x6D\x6D\x51\xC2\x45\xE4\x85\xB5\x76\x62\x5E\x7E\xC6\xF4\x4C\x42\xE9\xA6\x37\xED\x6B\x0B\xFF\x5C\xB6\xF4\x06\xB7\xED\xEE\x38\x6B\xFB\x5A\x89\x9F\xA5\xAE\x9F\x24\x11\x7C\x4B\x1F\xE6\x49\x28\x66\x51\xEC\xE4\x5B\x3D\xC2\x00\x7C\xB8\xA1\x63\xBF\x05\x98\xDA\x48\x36\x1C\x55\xD3\x9A\x69\x16\x3F\xA8\xFD\x24\xCF\x5F\x83\x65\x5D\x23\xDC\xA3\xAD\x96\x1C\x62\xF3\x56\x20\x85\x52\xBB\x9E\xD5\x29\x07\x70\x96\x96\x6D\x67\x0C\x35\x4E\x4A\xBC\x98\x04\xF1\x74\x6C\x08\xCA\x18\x21\x7C\x32\x90\x5E\x46\x2E\x36\xCE\x3B\xE3\x9E\x77\x2C\x18\x0E\x86\x03\x9B\x27\x83\xA2\xEC\x07\xA2\x8F\xB5\xC5\x5D\xF0\x6F\x4C\x52\xC9\xDE\x2B\xCB\xF6\x95\x58\x17\x18\x39\x95\x49\x7C\xEA\x95\x6A\xE5\x15\xD2\x26\x18\x98\xFA\x05\x10\x15\x72\x8E\x5A\x8A\xAC\xAA\x68\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF";
    Cryptokit.DH.g = "\002";
    Cryptokit.DH.privlen = 160;
  }

let dh_rand parameters () =
  Cryptokit.DH.private_secret ~rng:(Base.rng()) parameters

let dh_message parameters x =
  Cryptokit.DH.message parameters x

let dh_exp parameters a b =
  Cryptokit.DH.shared_secret parameters b a
