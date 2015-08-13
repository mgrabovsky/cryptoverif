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

let tunnel ic oc =
  print_string "Begin server.\n";flush stdout;
  let serv_id = "SSH-2.0-CV" in
  output_packet oc (serv_id^"\r\n");
  print ("S:id:"^serv_id);
  let s = input_line ic in
  let client_id = chop s in
  print ("C:id:"^client_id);
  if (String.sub client_id 0 8) <> "SSH-2.0-" then 
    begin
      Unix.shutdown_connection ic;
      failwith "Not an ssh client"
    end
  else
    begin
      let negociation_function = SSH_S.init () in
      let (key_exchange_reply_function, s) = 
	try
	  negociation_function () 
	with Cryptokit.Error Cryptokit.No_entropy_source ->
	  failwith "No entropy source!!!!"
      in
      output_packet oc s;
      print ("S:KEXINIT:"^s);

      let neg_packet = input_packet ic in
      print ("C:KEXINIT:"^neg_packet);

      let kex1 = input_packet ic in
      print ("C:KEXDH_INIT:"^kex1);
      
      let (new_key_function, s') = key_exchange_reply_function (client_id, serv_id, neg_packet, kex1) in
      output_packet oc s';
      print ("S:KEXDH_REPLY:"^s');

      let kex3 = input_packet ic in
      print ("C:NEWKEYS:"^kex3);
      
      let (tunnel_initialize_function, nk) = new_key_function kex3 in
      print ("S:NEWKEYS:"^nk);
      output_packet oc nk;
      create_tunnel (ic,oc) tunnel_initialize_function, Unix.descr_of_in_channel ic
    end

let userauth_failure = (string_of_char Ssh_crypto.tag_userauth_failure)^(Ssh_crypto.ssh_string "publickey")^"\000"

let userauth_success = (string_of_char Ssh_crypto.tag_userauth_success)

let parse_userauth_request username pk sid m =
  let (tag,i)=parse_message_tag m 0 in
  if tag <> Ssh_crypto.tag_userauth_request then
    failwith "expected userauth request"
  else
    begin
      let (username',i)=parse_string m i in
      let (service,i)=parse_string m i in
      let (methd,i)=parse_string m i in
        if service <> "ssh-connection" then
          failwith ("Service not supported: "^service)
        else
	  if (username' <> username) || (methd <> "publickey") then
            userauth_failure
          else
            let (b,i)=parse_bool m i in
            let (alg,i) = parse_string m i in
            let (pk',i) = parse_string m i in
              if (alg <> "ssh-rsa") then  
                (* we do not support this, return failure *)
                userauth_failure
              else if (pk <> (Ssh_crypto.pkey_from pk')) then
                (* wrong pk, return failure *)
                userauth_failure
              else
                begin
                  print "correct username, correct algorithm, correct pk";
                  (* verify signature *)
                  if b then
                    let (s,i') = parse_string m i in
                    let s=Ssh_crypto.signature_from s in
                    let ms=(Ssh_crypto.ssh_string sid)^(String.sub m 0 i) in
                      if Ssh_crypto.check ms pk s then
                        (*OK*)
			begin
			  print "userauth success";
                          userauth_success
                        end
                      else
                        userauth_failure
                  else
                    (string_of_char Ssh_crypto.tag_userauth_pk_ok)^(Ssh_crypto.ssh_string alg)^(Ssh_crypto.ssh_string pk')
                end
    end

let do_userauth (read_packet,write_packet) username pk sid =
  let m = read_packet () in
    if m <> (string_of_char Ssh_crypto.tag_service_request)^Ssh_crypto.ssh_userauth then
      failwith "expected service request"
    else
      begin
        write_packet ((string_of_char Ssh_crypto.tag_service_accept)^Ssh_crypto.ssh_userauth);

        let ok = ref false in
          while not !ok do
            let userauthreq_msg = read_packet () in
            let r=parse_userauth_request username pk sid userauthreq_msg in
              if r = userauth_success then
                ok := true;
              write_packet r;
          done
      end

let parse_channel_open m = 
  let (tag,i) =parse_message_tag m 0 in
  if tag <> Ssh_crypto.tag_channel_open then
    failwith ("channel open expected"^(String.escaped m))
  else
    let (sess,i)=parse_string m i in
    let (ch,i)=parse_int m i in
    let (ws,i)=parse_int m i in
    let (ps,i)=parse_int m i in
      if sess <> "direct-tcpip" then
        failwith "not supported"
      else
        let (host,i) = parse_string m i in
        let (port,i) = parse_int m i in
        let (origaddr,i) = parse_string m i in
        let (origport,i) = parse_int m i in
          (sess,ch,ws,ps,host,port,origaddr,origport)

let open_channel_confirm ch1 ch2 ws ps =
  (string_of_char Ssh_crypto.tag_channel_open_confirmation)^(Base.i2osp ch1 4)^(Base.i2osp ch2 4)^(Base.i2osp ws 4)^(Base.i2osp ps 4)

let manage_client_msgs socks ch ch_to_oc fd_to_ic read_packet write_packet =
  let r=read_packet () in
    print ("Received from client in tunnel: "^r);
  let tag,i = parse_message_tag r 0 in
    if tag = Ssh_crypto.tag_channel_open then
      let (sess,i)=parse_string r i in
      let (c,i)=parse_int r i in
      let (ws,i)=parse_int r i in
      let (ps,i)=parse_int r i in
        if sess <> "direct-tcpip" then
          failwith "not supported"
        else
          let (host,i) = parse_string r i in
          let (port,i) = parse_int r i in
          let (origaddr,i) = parse_string r i in
          let (origport,i) = parse_int r i in
            incr ch;
            Printf.printf "Port forwarding between %s:%d and %s:%d" host port origaddr origport;print_newline ();
            let (ic,oc) = Unix.open_connection (Unix.ADDR_INET (resolve host,port)) in
            let fd = Unix.descr_of_in_channel ic in
              Hashtbl.add fd_to_ic fd (ic,c);
              Hashtbl.add ch_to_oc (!ch) oc;
              socks := fd:: !socks;
              write_packet (open_channel_confirm c !ch 2000000 30000)
    else if tag = Ssh_crypto.tag_channel_data then
      let (c,i)=parse_int r i in
      let (m,i)=parse_string r i in
      let oc=Hashtbl.find ch_to_oc c in
        output_string oc m; flush oc

let manage_data s fd_to_ic write_packet =
  let (ic,c) = Hashtbl.find fd_to_ic s in
  let buf = String.create 1024 in
  let r = input ic buf 0 1024 in
    if r = 0 then
      begin
        write_packet ((string_of_char Ssh_crypto.tag_channel_close)^(Base.i2osp c 4));
        Hashtbl.remove fd_to_ic s
      end
    else
      begin
	let packet = ((string_of_char Ssh_crypto.tag_channel_data)^(Base.i2osp c 4)^(Ssh_crypto.ssh_string (String.sub buf 0 r))) in
	print ("Sending to client in tunnel: "^packet);	
	write_packet packet
      end
let do_connect (read_packet,write_packet) rfd =
  let ch = ref 0 in
  let socks = ref [] in
  let ch_to_oc = Hashtbl.create 10 in
  let fd_to_ic = Hashtbl.create 10 in
  while (true) do
    let (rl,_,_) = Unix.select (rfd::!socks) [] [] (-1.) in
      List.iter
        (fun s -> 
           if s = rfd then
             manage_client_msgs socks ch ch_to_oc fd_to_ic read_packet write_packet 
           else
             manage_data s fd_to_ic write_packet
        ) rl
  done

let ssh_server username pk ic oc =
  let ((read_packet,write_packet, sid), rfd) = tunnel ic oc in
    do_userauth (read_packet,write_packet) username pk sid;
    do_connect (read_packet,write_packet) rfd

let _ = 
  if (Array.length Sys.argv <> 5) then 
    failwith ("Usage "^(Sys.argv.(0))^" IP_address_to_bind port username_to_accept pk_to_accept")
  else
    let ip = resolve (Sys.argv.(1)) in
    let port = int_of_string (Sys.argv.(2)) in
    let username = Sys.argv.(3) in
    let pk = Ssh_crypto.pkey_from_file (Base.input_string_from_file Sys.argv.(4)) in
      Unix.establish_server (ssh_server username pk) (Unix.ADDR_INET (ip, port))
