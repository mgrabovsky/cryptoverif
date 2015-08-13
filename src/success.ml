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

(* check_usage can return the following results:
- raise Not_found, when secrecy cannot be proved, even by applying
  advised transformations
- add transformations to "advise", when secrecy cannot be proved
  in the current game, but may be provable by applying the transformations
  in "advise"
- leave "advise" empty when secrecy is proved in the current game.
*)


let advise = ref []

let whole_game = ref { proc = Terms.iproc_from_desc Nil; game_number = -1; current_queries = [] }

let rec check_usage_term seen_accu b t =
  match t.t_desc with
    Var(b',l) ->
      if b' == b then raise Not_found;
      List.iter (check_usage_term seen_accu b) l
  | ReplIndex _ -> ()
  | FunApp(f,l) ->
      List.iter (check_usage_term seen_accu b) l
  | TestE(t1,t2,t3) ->
      check_usage_term seen_accu b t1;
      check_usage_term seen_accu b t2;
      check_usage_term seen_accu b t3
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	List.iter (fun (_,l) -> List.iter (check_usage_term seen_accu b) l) def_list;
	check_usage_term seen_accu b t1;
	check_usage_term seen_accu b t2) l0;
      check_usage_term seen_accu b t3
  | LetE(PatVar b', { t_desc = Var(b'',l) }, t2, _) when b'' == b ->
      if not (List.memq b' (!seen_accu)) then
	begin
	  seen_accu := b' :: (!seen_accu);
	  try
	    check_usage_process seen_accu b' (!whole_game).proc
	  with Not_found ->
	    if List.length b'.def > 1 then
	      advise := Terms.add_eq (SArenaming b') (!advise)
	    else
	      raise Not_found
	end;
      List.iter (check_usage_term seen_accu b) l;
      check_usage_term seen_accu b t2
  | LetE(pat, t1, t2, topt) ->
      begin
	check_usage_pat seen_accu b pat;
	check_usage_term seen_accu b t1;
	check_usage_term seen_accu b t2;
	match topt with
	  None -> ()
	| Some t3 -> check_usage_term seen_accu b t3
      end
  | ResE(b,t) ->
      check_usage_term seen_accu b t
  | EventAbortE _ ->
      Parsing_helper.internal_error "Event_abort should have been expanded"

and check_usage_pat seen_accu b = function
    PatVar _ -> ()
  | PatTuple (f,l) -> List.iter (check_usage_pat seen_accu b) l
  | PatEqual t -> check_usage_term seen_accu b t

and check_usage_process seen_accu b p =
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      check_usage_process seen_accu b p1;
      check_usage_process seen_accu b p2
  | Repl(_,p) ->
      check_usage_process seen_accu b p
  | Input((c, tl), pat, p) ->
      List.iter (check_usage_term seen_accu b) tl;
      check_usage_pat seen_accu b pat;
      check_usage_oprocess seen_accu b p

and check_usage_oprocess seen_accu b p =
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(_,p) ->
      check_usage_oprocess seen_accu b p
  | Test(t,p1,p2) ->
      check_usage_term seen_accu b t;
      check_usage_oprocess seen_accu b p1;
      check_usage_oprocess seen_accu b p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list, t, p1) ->
	List.iter (fun (_,l) -> List.iter (check_usage_term seen_accu b) l) def_list;
	check_usage_term seen_accu b t;
	check_usage_oprocess seen_accu b p1) l0;
      check_usage_oprocess seen_accu b p2
  | Let(PatVar b', { t_desc = Var(b'',l) }, p1, _) when b'' == b ->
      if not (List.memq b' (!seen_accu)) then
	begin
	  seen_accu := b' :: (!seen_accu);
	  try
	    check_usage_process seen_accu b' (!whole_game).proc
	  with Not_found ->
	    if List.length b'.def > 1 then
	      advise := Terms.add_eq (SArenaming b') (!advise)
	    else
	      raise Not_found
	end;
      List.iter (check_usage_term seen_accu b) l;
      check_usage_oprocess seen_accu b p1
  | Let(pat,t,p1,p2) ->
      check_usage_pat seen_accu b pat;
      check_usage_term seen_accu b t;
      check_usage_oprocess seen_accu b p1;
      check_usage_oprocess seen_accu b p2
  | Output((c, tl),t2,p) ->
      List.iter (check_usage_term seen_accu b) tl;
      check_usage_term seen_accu b t2;
      check_usage_process seen_accu b p
  | EventP(t,p) ->
      (* Events are ignored when checking secrecy
	 This assumes that LetE/FindE have been expanded, so that
	 they do not occur in t *)
      check_usage_oprocess seen_accu b p
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

let has_assign b =
  List.exists (fun def ->
    match def.definition with
      DProcess { p_desc = Let _ } | DTerm { t_desc = LetE _} -> true
    | _ -> false) b.def



let check_secrecy b =
  let ty = ref None in
  advise := [];
  try
    List.iter (fun d -> 
      match d.definition with
	DProcess { p_desc = Let(PatVar _,{ t_desc = Var(b',_) },_,_) }
      |	DTerm { t_desc = LetE(PatVar _, { t_desc = Var(b',_) },_,_) } ->
	  if has_assign b' then
	    advise := Terms.add_eq (RemoveAssign (OneBinder b')) (!advise)
	  else if Terms.is_restr b' then
	    begin
	      (match !ty with
		None -> ty := Some b'.btype
	      |	Some ty' -> if ty' != b'.btype then 
		  Parsing_helper.internal_error ("Variable " ^ (Display.binder_to_string b) ^ " has definitions of different types"));
	      try
		check_usage_process (ref [b']) b' (!whole_game).proc
	      with Not_found ->
		if List.length b'.def > 1 then
		  advise := Terms.add_eq (SArenaming b') (!advise)
		else
		  raise Not_found
	    end
	  else
	    raise Not_found
      |	DProcess { p_desc = Restr _ } ->
	  (match !ty with
	    None -> ty := Some b.btype
	  | Some ty' -> if ty' != b.btype then 
	      Parsing_helper.internal_error ("Variable " ^ (Display.binder_to_string b) ^ " has definitions of different types"));
	  check_usage_process (ref [b]) b (!whole_game).proc
      |	_ ->
	  raise Not_found) b.def;
    if (!advise) == [] then
      begin
	print_string "Proved one-session secrecy of ";
	Display.display_binder b;
	print_newline();
	true
      end
    else
      begin
	List.iter (fun i -> 
	  Settings.advise := Terms.add_eq i (!Settings.advise)) (!advise);
	advise := [];
	false
      end
  with Not_found -> 
    advise := [];
    false

let check_query = function
    (QSecret1 b,_) -> (check_secrecy b, [])
  | (QSecret b,_) -> 
      let r1 = check_secrecy b in
      if r1 then
	let (r2, proba) = Facts.check_distinct b (!whole_game) in
	if r2 then
	  begin
	    print_string "Proved secrecy of ";
	    Display.display_binder b;
	    if proba != [] then
	      begin
		print_string " Probability: ";
		Display.display_set proba
	      end;
	    print_newline();
	    (true, proba)
	  end
	else (false, [])
      else (false, [])
  | (QEventQ(t1,t2),gn) ->
      let (r, proba) = Facts.check_corresp (t1,t2) (!whole_game) in
      if r then
	begin
	  print_string "Proved query ";
	  Display.display_query (QEventQ(t1,t2),gn);
	  if proba != [] then
	    begin
	      print_string " Probability: ";
	      Display.display_set proba
	    end;
	  print_newline();
	  (true, proba)
	end
      else (false, [])
  | (AbsentQuery,_) -> (false, [])	

(* Check query list takes a list of queries, tries to prove
   those that are not proved yet, and returns
    - the list of queries it proved
    - the updated list of all queries with their proofs
    - a boolean which is true when all queries have been proved *)

let rec check_query_list state = function
    [] -> ([],[],true)
  | ((a, poptref, popt)::l) ->
      let (l',l'',b) = check_query_list state l in
      match popt with
	Some _ -> (* The query was already proved before *)
	  (l', (a, poptref, popt)::l'', b)
      |	None -> (* We need to prove the query *)
	  let (res, proba) = check_query a in
	  if res then 
	    (* The query is proved *)
	    ((a,proba)::l', (a,poptref,Some(proba, state))::l'', b) 
	  else 
	    (* The query is not proved *)
	    (l', (a, poptref,popt)::l'', false)

let is_event_query f g = function
    ((QEventQ([false, { t_desc = FunApp(f',[{ t_desc = FunApp(f_tuple, []) }]) }], QTerm t_false),g'), _,_) -> 
      g == g' && f == f' && Terms.is_false t_false
  | _ -> false 

let rec update_full_proof query_list ((_,g), poptref, popt) =
  match popt, !poptref with
    Some(proba, state), None ->
      if is_full_proof query_list g proba state then
	poptref := Some(proba, state)
  | _ -> ()

and is_full_proof query_list g proba state =
  (List.for_all (is_full_proba query_list) proba) &&
  (is_full_state query_list g state)

and is_full_state query_list g state =
  if state.game == g then
    true
  else
    match state.prev_state with
      None -> Parsing_helper.internal_error "Game not found"
    | Some(_, proba, _, s') ->
        (List.for_all (is_full_proba query_list) proba) &&
	(is_full_state query_list g s')

and is_full_proba query_list = function
    SetProba _ -> true
  | SetEvent(f,g,poptref) ->
      match !poptref with
	Some _ -> true
      |	None ->
	  try
	    let query = List.find (is_event_query f g) query_list in
	    update_full_proof query_list query;
	    match !poptref with
	      Some _ -> true
	    | None -> false
	  with Not_found -> false


let is_success state =
  let g = state.game in
  whole_game := g;
  let vcounter = !Terms.vcounter in
  Terms.build_def_process None g.proc;
  let (proved_queries, all_queries, all_proved) = check_query_list state g.current_queries in
  g.current_queries <- all_queries; (* Updated queries *)
  List.iter (update_full_proof all_queries) all_queries;
  Terms.vcounter := vcounter; (* Forget created variables *)
  proved_queries, all_proved





