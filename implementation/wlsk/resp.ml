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

let server_fun cert_server_addr init_in init_out =
  let m1 = receive init_in in
  let o1 = WLSK_Resp.init() in
  let (o2, m2) = o1 m1 in
  send init_out m2;
  let m3 = receive init_in in
  let (o3, m41, m42, m43, m44) = o2 (Crypto.unconcat_str_str m3) in
  print_string "Contacting server...\n";
  flush stdout;
  let (in_cert, out_cert) = Unix.open_connection(cert_server_addr) in
  send out_cert (Base.compos [m41;m42;m43;m44]);
  let m5 = receive in_cert in
  Unix.shutdown_connection in_cert;
  close_in_noerr in_cert;
  close_out_noerr out_cert;
  print_string "Got reply.\n";
  flush stdout;
  let _ = o3 (Crypto.unconcat_str_str m5) in
  print_string ("OK. Initiator " ^ m1 ^" authenticated\n");
  flush stdout;
  Unix.shutdown_connection init_in;
  close_in_noerr init_in;
  close_out_noerr init_out;
  print_string "Done.\n"
  

let _ =
  if Array.length Sys.argv < 2 then 
    begin
      print_string "B expects the name of the server to contact\n";
      exit 2
    end;
  let responder = Crypto.get_hostname() in
  let responder_host = 
    try 
      Unix.gethostbyname responder
    with Not_found ->
      print_string ("Responder " ^ responder ^ " not found.\n");
      exit 2
  in
  let responder_addr = Unix.ADDR_INET(responder_host.Unix.h_addr_list.(0), responder_port) in
  let cert_server = Sys.argv.(1) in
  let cert_server_host = 
    try 
      Unix.gethostbyname cert_server
    with Not_found ->
      print_string ("Certificate server " ^ cert_server ^ " not found.\n");
      exit 2
  in
  let cert_server_addr = Unix.ADDR_INET(cert_server_host.Unix.h_addr_list.(0), cert_server_port) in
  print_string "Launching responder\n";
  flush stdout;
  Unix.establish_server (server_fun cert_server_addr) responder_addr
  
