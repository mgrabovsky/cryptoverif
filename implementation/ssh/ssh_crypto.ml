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
exception Encoding_error

let string_of_char = String.make 1

(* tag values *)

let tag_disconnect                  = '\001'     
let tag_ignore                      = '\002'     
let tag_unimplemented               = '\003'     
let tag_debug                       = '\004'     
let tag_service_request             = '\005'     
let tag_service_accept              = '\006'     
let tag_kex_init                    = '\020'     
let tag_newkeys                     = '\021'     
let tag_kexdh_init                  = '\030'
let tag_kexdh_reply                 = '\031'
let tag_userauth_request            = '\050'     
let tag_userauth_failure            = '\051'     
let tag_userauth_success            = '\052'     
let tag_userauth_banner             = '\053'     
let tag_userauth_pk_ok              = '\060'
let tag_global_request              = '\080'     
let tag_request_success             = '\081'     
let tag_request_failure             = '\082'     
let tag_channel_open                = '\090'     
let tag_channel_open_confirmation   = '\091'     
let tag_channel_open_failure        = '\092'     
let tag_channel_window_adjust       = '\093'     
let tag_channel_data                = '\094'     
let tag_channel_extended_data       = '\095'     
let tag_channel_eof                 = '\096'     
let tag_channel_close               = '\097'     
let tag_channel_request             = '\098'     
let tag_channel_success             = '\099'     
let tag_channel_failure             = '\100'     




(* this function returns the message with the padding and without the mac *)
let ssh_pad block_size payload = 
  let p = String.length payload in
  let mb = Base.ceildiv (p+9) block_size in (* minimal number of blocks *)
  let ms = mb * block_size in
  let padding_length = ms - (p + 5) in
  let packet_length = ms - 4 in
  let padding = Base.rand_string padding_length () in
  let s = String.create ms in
  Base.char4_of_int s 0 packet_length;
  s.[4] <- char_of_int padding_length;
  String.blit payload 0 s 5 p;
  String.blit padding 0 s (5+p) padding_length;
  s
    
(* this function takes the message and returns Some message or None if the message is malformed *)
let ssh_unpad m =
  if (String.length m < 5) then
    None
  else
    let packet_length = Base.int_of_char4 m 0 in
    let padding_length = int_of_char m.[4] in
    let p = packet_length - padding_length - 1 in
    if (padding_length < 4) || (p < 0) || (String.length m <> 4 + packet_length) then
      None
    else
      Some (String.sub m 5 p)

let concatm c s =
  (String.make 1 c)^s

let unconcatm s =
  (s.[0], String.sub s 1 ((String.length s)-1))

let concatn cookie neg =
  cookie^neg^"\000\000\000\000\000" (* bool = false, uint32 = 0 *)

let unconcatn m =
  if (String.length m < 21) then 
    raise Base.Match_fail
  else
    let cookie=String.sub m 0 16 in
    let neg = String.sub m 16 ((String.length m)-21) in
    (cookie, neg)


let ssh_string s = (Base.i2osp (String.length s) 4)^s
let string_of_ssh_string s = 
  if (String.length s < 4) then
    raise Base.Match_fail
  else
    let l=Base.int_of_char4 s 0 in
    if (String.length s <> 4+l) then
      raise Base.Match_fail
    else
      String.sub s 4 l

let rec strings_of_ssh_string s n =
  if n=0 then
    []
  else
    if (String.length s < 4) then
      raise Base.Match_fail
    else
      let l=Base.int_of_char4 s 0 in
      if (String.length s < 4+l) then
	raise Base.Match_fail
      else
	(String.sub s 4 l)::(strings_of_ssh_string (String.sub s (4+l) ((String.length s)-(4+l))) (n-1))
	  
let strings_of_ssh_string_ind s n i =
  strings_of_ssh_string (String.sub s i ((String.length s)-i)) n


let negotiation_string =
  (ssh_string "diffie-hellman-group14-sha1")^ (*kex_algorithms*)
    (ssh_string "ssh-rsa")^                   (*server_host_key_algorithms*)
    (ssh_string "aes128-cbc")^                (*encryption_algorithms_client_to_server*)
    (ssh_string "aes128-cbc")^                (*encryption_algorithms_server_to_client*)
    (ssh_string "hmac-sha1")^                 (*mac_algorithms_client_to_server*)
    (ssh_string "hmac-sha1")^                 (*mac_algorithms_server_to_client*)
    (ssh_string "none")^                      (*compression_algorithms_client_to_server*)
    (ssh_string "none")^                      (*compression_algorithms_server_to_client*)
    (ssh_string "")^                          (*languages_client_to_server*)
    (ssh_string "")                           (*languages_server_to_client*)

let ssh_userauth = ssh_string "ssh-userauth"
let ssh_connection = ssh_string "ssh-connection"

let check_algorithms s =
  true

let hash () = Cryptokit.hash_string (Cryptokit.Hash.sha1 ())

let add_000 s =
  let i = ref 0 in
  let l = String.length s in
  while !i < l && s.[!i] = '\000' do incr i done;
  if (l > !i) then
    if (((int_of_char s.[!i]) land 128) = 128) then
      "\000"^(String.sub s !i (l - !i)) 
    else
      (String.sub s !i (l - !i))
  else
    s

let mpint_of_g g = 
  ssh_string (add_000 g)

let g_of_mpint = string_of_ssh_string

let g_of_mpint_ind s i =
  match strings_of_ssh_string_ind s 1 i with
      [g] ->
	(g,i+4+(String.length g))
    | _ -> raise Base.Match_fail

type pkey = 
    { 
      psize : int;
      pe : string;
      pn : string;
    }

type skey = Cryptokit.RSA.key

let skey_to_pkey sk =
  { psize = sk.Cryptokit.RSA.size;
      pn  = sk.Cryptokit.RSA.n;
      pe  = sk.Cryptokit.RSA.e;}

let kgen ?e size () = 
  let k=Cryptokit.RSA.new_key ~rng:(Base.rng ()) ?e:e size in
  (skey_to_pkey k,k)
  

let bitsize s = 
  let i = ref 0 in
  while (s.[!i]='\000') do incr i; done;
  ((String.length s)- !i)*8

let pkey_from_ind s i = 
  match strings_of_ssh_string_ind s 3 i with
      |	[t;e;n] -> 
	if t = "ssh-rsa" then
	  ({
	    psize = bitsize n;
	    pn = n;
	    pe = e
	  }, i + 12 + (String.length t) + (String.length e) + (String.length n))
	else
	  raise Base.Match_fail
      | _ -> raise Base.Match_fail

let pkey_from s = 
  let (pk,_)=pkey_from_ind s 0 in pk

let pkey_to pk = 
  (ssh_string "ssh-rsa")^(mpint_of_g pk.pe)^(mpint_of_g pk.pn)

let rec p256 i =
  if i < 256 then 1
  else (p256 (i/256))+1

let asn_of_int i = 
  if i <= 127 then
    Base.i2osp i 1
  else
    let p = p256 i in
    (string_of_char (char_of_int (128+p)))^(Base.i2osp i p)

let int_of_asn s i =
  if (int_of_char s.[i]) land 128 = 128 then
    let size = (int_of_char s.[i]) land 127 in
    Base.osp2i s (i+1) size, i+1+size
  else
    int_of_char s.[i], i+1

let skey_begin_marker = "-----BEGIN RSA PRIVATE KEY-----\n"
let skey_bm_length = String.length skey_begin_marker
let skey_end_marker = "-----END RSA PRIVATE KEY-----\n"
let skey_em_length = String.length skey_end_marker


let asn_int s = "\x02"^(asn_of_int (String.length s))^s
let asn_sequence s = "\x30"^(asn_of_int (String.length s))^s

let get_asn_int s i = 
  if s.[i] <> '\x02' then
    raise Base.Match_fail
  else
    let size,i'=int_of_asn s (i+1) in
    String.sub s i' size,i'+size

let get_asn_sequence s i =
  if s.[i] <> '\x30' then
    raise Base.Match_fail
  else
    let size,i'=int_of_asn s (i+1) in
    String.sub s i' size,i'+size

let skey_from s =
  if (String.sub s 0 skey_bm_length) <> skey_begin_marker then
    raise Base.Match_fail
  else if (String.sub s ((String.length s)-skey_em_length) skey_em_length) <> skey_end_marker then
    raise Base.Match_fail
  else
    let b64 = Cryptokit.Base64.decode () in
    let str=String.sub s skey_bm_length ((String.length s)-skey_em_length-skey_bm_length) in
    b64#put_string str;
    b64#finish;
    let skb=b64#get_string in
    let sq,_ = get_asn_sequence skb 0 in
    let ver,i = get_asn_int sq 0 in
    if ver <> "\000" then
      raise Base.Match_fail
    else
      let n,i = get_asn_int sq i in
      let e,i = get_asn_int sq i in
      let d,i = get_asn_int sq i in
      let p,i = get_asn_int sq i in
      let q,i = get_asn_int sq i in
      let dp,i = get_asn_int sq i in
      let dq,i = get_asn_int sq i in
      let qinv,i = get_asn_int sq i in
      { Cryptokit.RSA.size = bitsize n; 
	Cryptokit.RSA.n = n; 
	Cryptokit.RSA.e = e;
	Cryptokit.RSA.d = d;
	Cryptokit.RSA.p = p;
	Cryptokit.RSA.q = q;
	Cryptokit.RSA.dp = dp;
	Cryptokit.RSA.dq = dq;
	Cryptokit.RSA.qinv = qinv}

let skey_to sk =
  let b=
    asn_sequence (
      (asn_int "\000")^
	(asn_int (add_000 sk.Cryptokit.RSA.n))^
	(asn_int (add_000 sk.Cryptokit.RSA.e))^
	(asn_int (add_000 sk.Cryptokit.RSA.d))^
	(asn_int (add_000 sk.Cryptokit.RSA.p))^
	(asn_int (add_000 sk.Cryptokit.RSA.q))^
	(asn_int (add_000 sk.Cryptokit.RSA.dp))^
	(asn_int (add_000 sk.Cryptokit.RSA.dq))^
	(asn_int (add_000 sk.Cryptokit.RSA.qinv)))
  in
  let b64=Cryptokit.Base64.encode_multiline () in
  b64#put_string b;
  b64#finish;
  skey_begin_marker^(b64#get_string)^skey_end_marker


let signature_from_ind s i =
  match strings_of_ssh_string_ind s 2 i with
    | [ssh_rsa;si] ->
      if ssh_rsa = "ssh-rsa" then
	si
      else
	raise Base.Match_fail
    | _ ->
      raise Base.Match_fail

let signature_from s = 
  signature_from_ind s 0

let signature_to s =
  (ssh_string "ssh-rsa")^(ssh_string s)

let concat3 pk g s =
  (ssh_string (pkey_to pk))^(mpint_of_g g)^(ssh_string (signature_to s))

let unconcat3 s =
  match strings_of_ssh_string_ind s 1 0 with
      [k] ->
	let pk=pkey_from k in
	let i = (String.length k) + 4 in
	let (g,i')=g_of_mpint_ind s i in
	(
	  match strings_of_ssh_string_ind s 1 i' with
	      [si] ->
		let s'=signature_from si in
		(pk,g,s')
	    | _ -> raise Base.Match_fail
	)
    | _ -> raise Base.Match_fail
	    
let concat8 vc vs ic is ks e f k =
  let s=(ssh_string vc)^(ssh_string vs)^(ssh_string ic)^(ssh_string is)^(ssh_string (pkey_to ks))^(mpint_of_g e)^(mpint_of_g f)^(mpint_of_g k) in
  s

let concatmsm = (^)
let concatem = (^)

let concatnm i s = (Base.i2osp i 4)^s

let emsa_pkcs1_v1_5_encode m emLen =
  let h = Cryptokit.hash_string (Cryptokit.Hash.sha1 ()) m in
  let t = "\x30\x21\x30\x09\x06\x05\x2b\x0e\x03\x02\x1a\x05\x00\x04\x14"^h
  in
  let tLen = String.length t in
  if (emLen < tLen + 11) then
    raise Encoding_error
  else
    let ps = String.make (emLen - tLen -3) '\xFF' in
    "\x00\x01"^ps^"\x00"^t


let rsassa_pkcs1_v1_5_sign sk m =
  let em = emsa_pkcs1_v1_5_encode m (Base.ceildiv sk.Cryptokit.RSA.size 8) in
  let s = Cryptokit.RSA.sign_CRT sk em in
  s

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

let rsassa_pkcs1_v1_5_verify pk m s =
  let k = Base.ceildiv pk.psize 8 in
  if String.length s <> k then
    begin
      (Printf.printf "%d : %d <> %d" pk.psize (String.length s) (k));
      print_newline ();
      false
    end
  else
    try
      let em = Cryptokit.RSA.unwrap_signature (pkey_to_key pk) s in
      let em' = emsa_pkcs1_v1_5_encode m k in
      em=em'
    with
	_ -> false

let sign m sk = 
  rsassa_pkcs1_v1_5_sign sk m

let check m pk s = 
  rsassa_pkcs1_v1_5_verify pk m s

let pkey_from_file s = 
  if (String.sub s 0 8 <> "ssh-rsa ") then 
    raise Encoding_error
  else
    let i = String.index_from s 9 ' ' in
    let tr=Cryptokit.Base64.decode () in
    tr#put_substring s 8 (i-8);
    tr#finish;
    pkey_from tr#get_string

let pkey_to_file pk =
  let ps=pkey_to pk in
  let tr = Cryptokit.Base64.encode_compact_pad () in
  tr#put_string ps;
  tr#finish;
  "ssh-rsa "^tr#get_string^" test@cv\n"
      
(*
K1 = HASH(K || H || "A" || session_id)
Kn = HASH(K || H || K1 || K2 || ... || Kn-1)
Key = K1 || K2 || ... || Kn
*)

let construct size tag () k h sid =
  let kh=(mpint_of_g k)^h in
  let rec construct_rec ki size =
    let ki' = Cryptokit.hash_string (Cryptokit.Hash.sha1 ()) (kh^ki) in
    if (size <= 20) then
      ki^(String.sub ki' 0 size)
    else
      construct_rec (ki^ki') (size-20)
  in
  let k1 = Cryptokit.hash_string (Cryptokit.Hash.sha1 ()) (kh^tag^sid) in
  if (size <= 20) then
    String.sub k1 0 size
  else
    construct_rec k1 (size-20)


let encrypt_transform = ref None
let decrypt_transform = ref None

let symenc m key iv = 
  let t = Cryptokit.Cipher.aes ~mode:Cryptokit.Cipher.CBC ~iv:iv key Cryptokit.Cipher.Encrypt in
    t#put_string m;
    t#flush;
    t#get_string

let symdec m key iv =
  let t = Cryptokit.Cipher.aes ~mode:Cryptokit.Cipher.CBC ~iv:iv key Cryptokit.Cipher.Decrypt in
    try 
      t#put_string m;
      t#flush;
      Some (t#get_string)
    with 
	_ -> None

let mac = Crypto.mac (Cryptokit.MAC.hmac_sha1)
let check_mac = Crypto.mac_check (Cryptokit.MAC.hmac_sha1)

let get_size m = Base.int_of_char4 m 0 
