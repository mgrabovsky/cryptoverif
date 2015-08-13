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
open Base

type pkey = string
type skey = string

let time msg f =
  let t1 = Sys.time () in
  let result = f () in
  let t2 = Sys.time () in
  Printf.eprintf "Time elapsed (%s): %f" msg (t2 -. t1);
  result

let pkey_from x=x
let pkey_to x=x
let skey_from x=x
let skey_to x=x

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

let concat_pk_str=concat_str_str
let unconcat_pk_str=unconcat_str_str

let get_hostname = Unix.gethostname

let dummy1 a arg=
  compos [a;arg]

let dummy2 a arg1 arg2=
  compos [a;arg1;arg2]

let dummy3 a arg1 arg2 arg3=
  compos [a;arg1;arg2;arg3]

let inv_dummy1 a x =
  match decompos x with
      [a';a1] -> 
        if (a=a') then a1 
        else raise Match_fail
    | _ -> raise Match_fail

let inv_dummy2 a x =
  match decompos x with
      [a';a1;a2] -> 
        if (a=a') then (a1,a2) 
        else raise Match_fail
    | _ -> raise Match_fail

let inv_dummy3 a x =
  match decompos x with
      [a';a1;a2;a3] -> 
        if (a=a') then (a1,a2,a3) 
        else raise Match_fail
    | _ -> raise Match_fail

let pad _ _ = dummy1 "pad"
let pad_inv _ = inv_dummy1 "pad"
let sym_kgen = id
let sym_enc _ =dummy2 "sym_enc"
let sym_dec _ msg k =
  try 
    let m,k'=inv_dummy2 "sym_enc" msg in
      if k=k' then Some m else None 
  with _ -> None
let sym_r_enc _=dummy3 "sym_r_enc"
let sym_r_dec _ _ msg k =
  try 
    let m,k',r=inv_dummy3 "sym_r_enc" msg in
      if k=k' then Some m else None 
  with _ -> None

let mac_kgen=id
let mac _=dummy2 "mac"
let mac_check _ m k mac =
  try
    let m',k' = inv_dummy2 "mac" mac in
      if m = m' && k=k' then true else false
  with _ -> false

let pk_kgen _ () = 
  let r=rand_string 1 () in
    (dummy1 "pk" r,dummy1 "sk" r)

let pk_enc = dummy2 "pk_enc"
let pk_dec c sk = 
  try 
    let (m,pk) = inv_dummy2 "pk_enc" c in
    let rp = inv_dummy1 "pk" pk in
    let rs = inv_dummy1 "sk" sk in
      if rp = rs then
        Some m
      else
        None
  with
      Match_fail -> None

let pk_sign _ _ = dummy2 "pk_sign" 
let pk_check_sign _ _ msg pk s =
  try
    let (m,sk) = inv_dummy2 "pk_sign" s in
    let rp = inv_dummy1 "pk" pk in
    let rs = inv_dummy1 "sk" sk in
      (rp = rs) && (m = msg)
  with _ -> false

let rsassa_pss_sign _ = dummy2 "rsassa_pss_sign" 
let rsassa_pss_verify _ msg pk s =
  try
    let (m,sk) = inv_dummy2 "rsassa_pss_sign" s in
    let rp = inv_dummy1 "pk" pk in
    let rs = inv_dummy1 "sk" sk in
      (rp = rs) && (m = msg)
  with _ -> false


type dh_parameters = string
type dh_secret = string

let dh_group14 = "dh_group14"

let dh_new_parameters ?rng:(rng=Base.rng ()) ?privlen:(privlen=160) size =
  Base.compos ["dh_new_parameters";string_of_int privlen;string_of_int size]

let dh_rand params () =
  Base.compos ["dh_rand"; params; Base.rand_string 1 ()]

let dh_message params secret =
  Base.compos ["g^";secret]

let dh_exp params str secret =
  let x= inv_dummy1 "g^" str in
  if x>secret then
    Base.compos ["shared_secret";x;secret]
  else
    Base.compos ["shared_secret";secret;x]
