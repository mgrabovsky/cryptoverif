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
open Lexing

exception IllegalCharacter
exception IllegalEscape
exception UnterminatedString

let accept_arobase = ref false

let internal_error mess =
  print_string ("Internal error: " ^ mess ^ "\nPlease report bug to Bruno.Blanchet@inria.fr, including input file and output\n");
  exit 3

(* extent, for error messages *)

type extent = Lexing.position * Lexing.position

exception Error of string * extent

let dummy_ext = (Lexing.dummy_pos, Lexing.dummy_pos)

let next_line lexbuf =
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with 
			 pos_bol = lexbuf.lex_curr_p.pos_cnum;
			 pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1 }

let extent lexbuf = 
  (Lexing.lexeme_start_p lexbuf,
   Lexing.lexeme_end_p lexbuf)

let parse_extent () =
  (Parsing.symbol_start_pos(),
   Parsing.symbol_end_pos())

let combine_extent ((outer_start, _) as outer_ext) ((inner_start, inner_end) as inner_ext) =
  if inner_ext == dummy_ext then outer_ext else
  if outer_ext == dummy_ext then inner_ext else
  ({ outer_start with 
     pos_cnum = outer_start.pos_cnum + inner_start.pos_cnum + 1 },
   { outer_start with 
     pos_cnum = outer_start.pos_cnum + inner_end.pos_cnum + 1 })

let display_error mess (loc_start, loc_end) =
  if loc_start.pos_cnum = -1 then
    Printf.printf "Error: %s\n" mess
  else
    Printf.printf "Character %d - character %d:\nError: %s\n"
      loc_start.pos_cnum
      loc_end.pos_cnum
      mess

let in_file_position (def_start,_) (loc_start, loc_end) =
  if loc_start.pos_cnum = -1 then
    "<unknown>"
  else
    if loc_start.pos_fname = def_start.pos_fname then
      Printf.sprintf "line %d, character %d - line %d, character %d"
	loc_start.pos_lnum (loc_start.pos_cnum - loc_start.pos_bol +1)
	loc_end.pos_lnum (loc_end.pos_cnum - loc_end.pos_bol+1)
    else
      Printf.sprintf "file \"%s\", line %d, character %d - line %d, character %d"
	loc_start.pos_fname
	loc_start.pos_lnum (loc_start.pos_cnum - loc_start.pos_bol +1)
	loc_end.pos_lnum (loc_end.pos_cnum - loc_end.pos_bol+1)


let file_position (loc_start, loc_end) =
  if loc_start.pos_cnum = -1 then
    "<unknown>"
  else
    Printf.sprintf "File \"%s\", line %d, character %d - line %d, character %d"
      loc_start.pos_fname
      loc_start.pos_lnum (loc_start.pos_cnum - loc_start.pos_bol +1)
      loc_end.pos_lnum (loc_end.pos_cnum - loc_end.pos_bol+1)

let input_error mess (loc_start, loc_end) =
  if loc_start.pos_cnum = -1 then
    Printf.printf "Error: %s\n" mess
  else
    Printf.printf "%s:\nError: %s\n"
      (file_position (loc_start, loc_end))
      mess;
  exit 2

let input_warning mess (loc_start, loc_end) =
  if loc_start.pos_cnum = -1 then
    Printf.printf "Warning: \n%s\n" mess
  else
    Printf.printf "%s:\nWarning: %s\n"
      (file_position (loc_start, loc_end))
      mess

let user_error mess =
  print_string mess;
  exit 2

let buf = ref (String.create 64)
let index = ref 0

let clear_buffer () =
  buf := String.create 64;
  index := 0

let get_string () =
  let s=String.sub (!buf) 0 (!index) in
    clear_buffer ();
    s

let add_char c =
    begin
      let buf_len = String.length (!buf) in
        if !index >= buf_len then
          let new_buf = String.create (buf_len * 2) in
            String.blit !buf 0 new_buf 0 buf_len;
            buf := new_buf
    end;
  (!buf).[!index] <- c;
  index := (!index) + 1

let char_backslash = function
    'n' -> '\n'
  | 't' -> '\t'
  | 'b' -> '\b'
  | 'r' -> '\r'
  | c -> c

