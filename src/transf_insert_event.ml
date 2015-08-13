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
open Types

(***** Manual insertion of abort event *****)

let rec replace_process count occ premp p =
  { i_desc = 
    begin
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) -> 
      Par(replace_process count occ premp p1,
	  replace_process count occ premp p2)
  | Repl(b,p) ->
      Repl(b, replace_process count occ premp p)
  | Input(c, pat, p) ->
      Input(c, pat, replace_oprocess count occ premp p)
    end;
    i_occ = p.i_occ;
    i_facts = None }

and replace_oprocess count occ premp p =
  if p.p_occ == occ then
    begin
      incr count;
      premp
    end
  else
    { p_desc = 
      begin
    match p.p_desc with
      Yield -> Yield
    | EventAbort f -> EventAbort f
    | Restr(b,p) -> Restr(b, replace_oprocess count occ premp p)
    | Test(t,p1,p2) -> Test(t, replace_oprocess count occ premp p1,
			    replace_oprocess count occ premp p2)
    | Find(l0,p2,find_info) ->
	Find(List.map (fun (bl,def_list,t,p1) ->
	       (bl,def_list,t,
	        replace_oprocess count occ premp p1)) l0,
	     replace_oprocess count occ premp p2, find_info)
    | Output(c,t,p) ->
	Output(c,t,replace_process count occ premp p)
    | Let(pat,t,p1,p2) ->
	Let(pat,t,replace_oprocess count occ premp p1,
	    replace_oprocess count occ premp p2)
    | EventP(t,p) ->
	EventP(t,replace_oprocess count occ premp p)
    | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
      end;
      p_occ = p.p_occ;
      p_facts = None  }

let insert_event occ s g =
  let f = { f_name = s;
	    f_type = [Settings.t_bitstring],Settings.t_bool;
	    f_cat = Event;
	    f_options = 0;
	    f_statements = [];
	    f_collisions = [];
	    f_eq_theories = NoEq;
            f_impl = No_impl;
            f_impl_inv = None }
  in
  let idx = Terms.build_term_type Settings.t_bitstring (FunApp(Settings.get_tuple_fun [], [])) in
  let t = Terms.build_term_type Settings.t_bool (FunApp(f, [idx])) in
  let premp = Terms.oproc_from_desc(EventAbort(f)) in
  let count = ref 0 in
  let p' = replace_process count occ premp g.proc in
  if (!count) = 0 then 
    raise (Parsing_helper.Error("Occurrence " ^ (string_of_int occ) ^ " not found. You should use the command show_game occ to determine the desired occurrence.", Parsing_helper.dummy_ext))
  else if (!count > 1) then
    raise (Parsing_helper.Error("Occurrence " ^ (string_of_int occ) ^ " ambiguous. You should use the command show_game occ to determine the desired occurrence.", Parsing_helper.dummy_ext))
  else
    begin
      Settings.changed := true;
      let g' = { proc = p'; game_number = -1; current_queries = [] } in
      let q_proof = ref None in
      g'.current_queries <- ((QEventQ([false, t], QTerm (Terms.make_false())), g'), q_proof, None) :: g.current_queries;
      (g', [SetEvent(f, g', q_proof)], [DInsertEvent(f,occ)])
    end
