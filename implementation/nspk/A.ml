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
let responder_port = 0x8081
let cert_server_port = 0x8082

let send ch s =
  output_binary_int ch (String.length s);
  output_string ch s;
  flush ch

let receive ch =
  let len = input_binary_int ch in
  let s = String.create len in
  really_input ch s 0 len;
  s

let _ =
  if Array.length Sys.argv < 3 then 
    begin
      print_string "A expects the name of the responder and of the certificate server to contact\n";
      exit 2
    end;
  let responder = Sys.argv.(1) in
  let responder_host = 
    try 
      Unix.gethostbyname responder
    with Not_found ->
      print_string ("Responder " ^ responder ^ " not found.\n");
      exit 2
  in
  let responder_addr = Unix.ADDR_INET(responder_host.Unix.h_addr_list.(0), responder_port) in
  let cert_server = Sys.argv.(2) in
  let cert_server_host = 
    try 
      Unix.gethostbyname cert_server
    with Not_found ->
      print_string ("Certificate server " ^ cert_server ^ " not found.\n");
      exit 2
  in
  let cert_server_addr = Unix.ADDR_INET(cert_server_host.Unix.h_addr_list.(0), cert_server_port) in
  let id_resp = Crypto.concat_str_str responder "B" in
  let oa1 = ONS_A.init() in
  print_string "Contacting certificate server...\n";
  flush stdout;
  let (oa3,m11,m12) = oa1 id_resp in
  let (in_cert, out_cert) = Unix.open_connection(cert_server_addr) in
  print_string "Connection open"; print_newline();
  send out_cert (Crypto.concat_str_str m11 m12);
  let m2 = receive in_cert in
  Unix.shutdown_connection in_cert;
  close_in_noerr in_cert;
  close_out_noerr out_cert;
  print_string "Got reply.";
  flush stdout;
  let (m21,m22,m23) = Crypto.unconcat_str_str_str m2 in
  let m21key = Crypto.pkey_from m21 in
  let (oa5, m3) = oa3 (m21key, m22, m23) in
  print_string (" Certificate correct.\nContacting responder "^responder^"...\n"); 
  flush stdout;
  let (in_resp, out_resp) = Unix.open_connection(responder_addr) in
  send out_resp m3;
  let m6 = receive in_resp in
  print_string "Responder authenticated\n";
  flush stdout;
  let (_,m7) = oa5 m6 in
  send out_resp m7;
  Unix.shutdown_connection in_resp;
  close_in_noerr in_resp;
  close_out_noerr out_resp;
  print_string "Done.\n"
  
  
