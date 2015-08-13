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

let is_alphabetic c=
  (c>='A' && c <='Z') || (c>='a' && c <='z') || (c>='0' && c <='9')

let hex_of_char c=
  Printf.sprintf "%02x" (int_of_char c)

let rec string_fold f s r=
  match s with 
      "" -> r
    | s -> (f s.[0] (string_fold f (String.sub s 1 ((String.length s)-1)) r))

let alphabetize_string (s:string) =
  string_fold 
    (
      fun (c:char) (s:string) -> 
        if is_alphabetic c then 
          (String.make 1 c)^s 
        else 
          ("_"^(hex_of_char c)^s)
    ) s ""

let rec heuristic_decompos (s:string) =
  if String.length s>=4 && s.[0] = '\000' && s.[1] = '\000' && s.[2] = '\000' && s.[3] <> '\000' && s.[3] <= '\004' then
    let l = Base.decompos s in
      print_string "(";
      heuristic_decompos_list l;
      print_string ")";
  else
    print_string (alphabetize_string s)

and heuristic_decompos_list = function
  | [] -> ()
  | [x] -> heuristic_decompos x
  | x::l -> heuristic_decompos x;print_string ",";heuristic_decompos_list l

and heuristic_decompos_list_list = function
  | [] -> ()
  | [x] -> heuristic_decompos_list x
  | x::l -> heuristic_decompos_list x;print_string ";";heuristic_decompos_list_list l

let _ =
print_string "start...";print_newline ();
let start = WLSK_keygen.init () in
start (Unix.gethostname());
print_string "enc_key=";heuristic_decompos (Base.input_string_from_file "wlsk_enc_key");
print_string ",mac_key=";heuristic_decompos (Base.input_string_from_file "wlsk_mac_key");
print_string ",table=";heuristic_decompos_list_list (Base.get_from_table "keytbl" Base.id);
print_newline ();
print_string "A1...";print_newline ();
let a1=WLSK_Init.init () in
let a3,idA = a1 (Unix.gethostname()) in
print_string "idA=";heuristic_decompos idA;print_newline ();
print_string "B2...";print_newline ();
let b2=WLSK_Resp.init () in
let (b4,n)=b2 (idA) in
print_string "n=";heuristic_decompos n;print_newline ();
print_string "A3...";print_newline ();
let (_,e,m)=a3 (n) in
print_string "e=";heuristic_decompos e;print_string ",m=";heuristic_decompos m;print_newline ();
print_string "B4...";print_newline ();
let (b6,idA',idB',e',m')=b4 (e, m) in
print_string "idA'=";heuristic_decompos idA';print_string ",idB'=";heuristic_decompos idB';print_string ",e'=";heuristic_decompos e';print_string ",m'=";heuristic_decompos m';print_newline ();
print_string "S5...";print_newline ();
let s5=WLSK_S.init () in
let (_,e'',m'')=s5 (idA', idB', e', m') in
print_string "e''=";heuristic_decompos e'';print_string ",m''=";heuristic_decompos m'';print_newline ();
print_string "B6...";print_newline ();
let _ = b6 (e'', m'') in ()
