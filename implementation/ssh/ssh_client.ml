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
open Ssh_network

let print s =
  print_string (String.escaped s);
  print_newline ()

let tunnel ip port = 
    let (ic,oc) = Unix.open_connection (Unix.ADDR_INET (ip, port)) in
    print_string "Connected.\n";flush stdout;
    let s = input_line ic in
    let serv_id = chop s in
    let client_id = "SSH-2.0-CV" in
    print ("S:id:"^serv_id);
    if (String.sub serv_id 0 8) <> "SSH-2.0-" then 
      (
        Unix.shutdown_connection ic;
        failwith "The server is no SSH server !"
      )
    else
      begin
        print ("C:id:"^client_id);
        output_packet oc (client_id^"\r\n");
        
        let negociation_function = SSH_C.init () in
        let (key_exchange_init_function, s) = negociation_function () in
        print ("C:KEXINIT:"^s);

        let neg_packet = input_packet ic in
        print ("S:KEXINIT:"^neg_packet);
        
        output_packet oc s;
        let (new_key_function, s') = key_exchange_init_function neg_packet in
        output_packet oc s';
        print ("C:KEXDH_INIT:"^s');
  
        let kex2= input_packet ic in
        print ("S:KEXDH_REPLY:"^kex2);
        
        let (tunnel_init_function,nkm)=new_key_function (client_id, serv_id, kex2) in
        print ("C:NEWKEYS:"^nkm);
        output_packet oc nkm;
  
        let nkm2 = input_packet ic in
        print ("S:NEWKEYS:"^nkm2);
        create_tunnel (ic,oc) (fun () -> tunnel_init_function nkm2), Unix.descr_of_in_channel ic
      end

(* userauth : returns true if the message is a userauth_success message *)
let is_success m = String.length m = 1 && m.[0]=Ssh_crypto.tag_userauth_success

(* userauth : takes a failure message, and returns whether publickey is available *)
let publickey_available m = 
  let tag,i = parse_message_tag m 0 in
  if tag = Ssh_crypto.tag_userauth_failure then 
  
    (* can we use "publickey" ? *)
    let m',i = parse_string m i in
    List.mem "publickey" (Str.split (Str.regexp ",") m')
  else
    failwith "user_auth success or failure expected"

(* userauth: returns an auth request message *)
let userauth_request_msg username methd =
  (string_of_char Ssh_crypto.tag_userauth_request)^(Ssh_crypto.ssh_string username)^(Ssh_crypto.ssh_connection)^(Ssh_crypto.ssh_string methd)

let userauth_request_msg_pk username sk b sid =
  let m=(userauth_request_msg username "publickey")^(if b then "\001" else "\000")^(Ssh_crypto.ssh_string "ssh-rsa")^(Ssh_crypto.ssh_string (Ssh_crypto.pkey_to (Ssh_crypto.skey_to_pkey sk))) in
  if b then
    let ms= (Ssh_crypto.ssh_string sid)^m in
    let s = Ssh_crypto.sign ms sk in
      m^(Ssh_crypto.ssh_string (Ssh_crypto.signature_to s))
  else
    m

let is_pk_ok m sk =
  let (tag,i)=parse_message_tag m 0 in
  if tag <> Ssh_crypto.tag_userauth_pk_ok then
    false
  else
    let (alg,i) = parse_string m i in
    let (pk',i) = parse_string m i in
      if alg <> "ssh-rsa" then
        false
      else if (Ssh_crypto.pkey_from pk' <> Ssh_crypto.skey_to_pkey sk) then
        false
      else
        true


let do_userauth username sk sid (read_packet, write_packet) =
  write_packet ((string_of_char Ssh_crypto.tag_service_request)^Ssh_crypto.ssh_userauth);
  let service_accept_msg= read_packet () in
    if service_accept_msg <>  (string_of_char Ssh_crypto.tag_service_accept)^Ssh_crypto.ssh_userauth then
      failwith "service not accepted"
    else
      write_packet (userauth_request_msg username "none");
      let response1 = read_packet () in
        if is_success response1 then 
          true
        else
          if publickey_available response1 then
            let m = userauth_request_msg_pk username sk false sid in
              write_packet m;
              let r = read_packet () in
                if (is_pk_ok r sk) then
                  let m'=  userauth_request_msg_pk username sk true sid in
                    write_packet m';
                    let r' = read_packet () in
                      if (is_success r') then 
                        true
                      else
                        false
                else
                  false
          else
            failwith "no publickey possible"


let open_connection chan iph porth hostr portr= 
  (string_of_char Ssh_crypto.tag_channel_open)^
    (Ssh_crypto.ssh_string "direct-tcpip")^
    chan^
    (Base.i2osp 2000000 4)^
    (Base.i2osp 32768 4)^
    (Ssh_crypto.ssh_string hostr)^
    (Base.i2osp portr 4)^
    (Ssh_crypto.ssh_string (Unix.string_of_inet_addr iph))^
    (Base.i2osp porth 4)

let disconnect code = (string_of_char Ssh_crypto.tag_disconnect)^(Base.i2osp code 4)^(Ssh_crypto.ssh_string "")^(Ssh_crypto.ssh_string "")

let response_success m = 
  if (String.length m <> 1 && (m.[0]=Ssh_crypto.tag_request_success || m.[0] =Ssh_crypto.tag_request_failure)) then 
    failwith "expected request_success or request_failure"
  else
    if m.[0] = Ssh_crypto.tag_request_success then
      true
    else 
      false

let manage_accept write_packet serv_sock hostr portr ch_to_fd ch =
  let (client_sock,client_addr) = Unix.accept serv_sock in
    incr ch;
    let (ip,port)=match Unix.getpeername client_sock with
        Unix.ADDR_INET (ip,port) -> ip,port
      | _ -> failwith "getpeername not ADDR_INET family"
    in
      Hashtbl.add ch_to_fd !ch client_sock;
      print ("accepted connection: "^(Unix.string_of_inet_addr ip)^":"^(string_of_int port));
      let packet = open_connection (Base.i2osp !ch 4) ip port hostr portr in
        print ("open_connection: "^packet);
        write_packet packet

let manage_server_message read_packet ch_to_fd fd_to_ch socks =
  let r = read_packet () in
    print ("Received from server in tunnel: "^r);
  let (tag, i) = parse_message_tag r 0 in
    if tag = Ssh_crypto.tag_channel_open_confirmation then (* server accepted our connection *)
      let (c1,i) = parse_int r i in
      let (c2,i) = parse_int r i in
      let (ws,i) = parse_int r i in
      let (max_size,_) = parse_int r i in
        Printf.printf "accepted: %d,%d,%d,%d\n" c1 c2 ws max_size;
        let sock=Hashtbl.find ch_to_fd c1 in
          socks :=  sock :: !socks;
          Hashtbl.add fd_to_ch sock c2
            
    else if tag = Ssh_crypto.tag_channel_open_failure then (* server rejected our connection *)
      let (c,i)=parse_int r i in
      let (rc,i)=parse_int r i in
      let (reason,i)=parse_string r i in
      let sock = Hashtbl.find ch_to_fd c in
        Unix.shutdown sock Unix.SHUTDOWN_SEND;
        failwith ((string_of_int rc)^": "^(String.escaped reason))
    else if tag = Ssh_crypto.tag_channel_data then (* server wrote something in a channel, need to write that to the correct fd *)
      let (c,i)=parse_int r i in
      let (m,i)=parse_string r i in
      let sock=Hashtbl.find ch_to_fd c in
      let sent = Unix.write sock m 0 (String.length m) in
        if sent <> String.length m then
          failwith "Could not write everything"
        else
          ()
    else 
      (
        print ("Message not parsed: "^r);
        failwith "Message not parsed"
      )
        
let manage_client_data write_packet fd_to_ch s =
  let ch = Hashtbl.find fd_to_ch s in
  let buf = String.create 1024 in
  let r = Unix.read s buf 0 1024 in
  let packet = ((string_of_char Ssh_crypto.tag_channel_data)^(Base.i2osp ch 4)^(Ssh_crypto.ssh_string (String.sub buf 0 r))) in
    print ("Sending to server in tunnel: "^packet);
    write_packet packet

   
        
let do_connect (read_packet, write_packet) rfd iph porth hostr portr =
  (* requesting port forwarding authorization *)

  let serv_sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    Unix.set_nonblock serv_sock;
    Unix.bind serv_sock (Unix.ADDR_INET (iph,porth));
    Unix.listen serv_sock 10;
    let ch_to_fd = Hashtbl.create 10 in
    let fd_to_ch = Hashtbl.create 10 in
    let socks = ref [] in
    let ch = ref 0 in
      try
        while true do
          let (rl,_,_) = Unix.select (rfd::serv_sock::!socks) [] [] (-1.) in
            List.iter 
              (fun s -> 
                 if s = serv_sock then (*New connection: accept it *)
                   manage_accept write_packet serv_sock hostr portr ch_to_fd ch
                 else if s = rfd then (*something to read from ssh server*)
                   manage_server_message read_packet ch_to_fd fd_to_ch socks
                 else (* we read data from a socket *)
                   manage_client_data  write_packet fd_to_ch s
              ) rl
        done
      with
        | exn -> 
            Unix.shutdown serv_sock Unix.SHUTDOWN_RECEIVE;
            raise exn

let _ =
  if (Array.length Sys.argv <> 8) then 
    failwith ("Usage "^(Sys.argv.(0))^" IP_address_to_connect_to port username sk bind_port redirected_host redirected_port")
  else
    let ip = resolve (Sys.argv.(1)) in
    let port = int_of_string (Sys.argv.(2)) in
    let username = Sys.argv.(3) in
    let sk = Ssh_crypto.skey_from (Base.input_string_from_file Sys.argv.(4)) in
    let porth = int_of_string (Sys.argv.(5)) in
    let hostr = Sys.argv.(6) in
    let portr = int_of_string (Sys.argv.(7)) in

    let ((read_packet,write_packet,sid),rfd) = tunnel ip port in
    if not (do_userauth username sk sid (read_packet,write_packet)) then
      failwith "userauth failed"
    else
      begin
        print "userauth ok!";
        do_connect (read_packet,write_packet) rfd ip porth hostr portr
      end
