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

let resolve name =
  try
    let resolution = Unix.gethostbyname name in
      resolution.Unix.h_addr_list.(0) (* return the first IP address resolved to the name name *)
  with Not_found ->
    failwith ("Could not resolve "^name^".")

let input_packet ic =
  let buf1 = String.create 4 in
  really_input ic buf1 0 4;
  let n = Base.int_of_char4 buf1 0 in
  let buf2 = String.create n in
  really_input ic buf2 0 n;
  buf1^buf2

let output_packet oc s =
  output_string oc s; flush oc

let rec chop s =
  let l = String.length s in
  if s.[l-1] = '\r' || s.[l-1] = '\n' then
    chop (String.sub s 0 (l-1))
  else
    s

let input_blocks ic size =
  if size <> 0 then
    let buf=String.create size in
      really_input ic buf 0 size;
      buf
  else
    ""
  
let input_block ic = input_blocks ic 16

let input_mac ic = input_blocks ic 20

let create_tunnel (ic,oc) tunnel_initialize_function =
  let ((tunnel_write_function, tunnel_read1_function), iv12, iv21, sid) = tunnel_initialize_function () in
  let riv12 = ref iv12 in
  let riv21 = ref iv21 in
  let m12 = ref 3 in
  let m21 = ref 3 in
      let read_packet () =
        
        let p1 = input_block ic in
        let (tunnel_read2_function, size) = tunnel_read1_function (p1, !riv21) in
          riv21 := p1;
          if (size > 30000 || size < 12 || size mod 16 <> 12) then
            failwith ("Malformed packet, size = "^(string_of_int size))
          else
            let p2 = input_blocks ic (size-12) in
            let mm = input_mac ic in
            let ((),r) = tunnel_read2_function (p2, !riv21, mm, !m21) in
              if String.length p2 <> 0 then 
                riv21 := String.sub p2 ((String.length p2) - 16) 16;
              incr m21;
              r
      in
      let write_packet m =
        let ((),r) = tunnel_write_function (m, !riv12, !m12) in
          incr m12;
          riv12 := String.sub r ((String.length r) - 36) 16;
          output_string oc r; flush oc;
      in
        (read_packet,write_packet,sid)

let string_of_char c = String.make 1 c


let parse_message_tag m i = 
  (m.[i],i+1)

let parse_int m i =
  (Base.osp2i m i 4, i + 4)

let parse_string m i =
  let s = match Ssh_crypto.strings_of_ssh_string_ind m 1 i with
    | [s] -> s
    | _ -> failwith "malformed message"
  in
  let i=i+4+(String.length s) in
    (s,i)

let parse_bool m i=
  let b=m.[i]<>'\000' in
    (b,i+1)
