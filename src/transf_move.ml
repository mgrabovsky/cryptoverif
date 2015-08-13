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

(* Move new and let: 
   (1) when a restriction has several uses under different
   branches of if/find, move it down under if/find.  It will be later
   SA renamed, which can allow to distinguish cases easily.
   (2) when a variable defined by let has no array reference and is used only in
   one branch of a if/let/find, we move it under the if/let/find to reduce
   the number of cases in which it is computed.
  *)

let done_transfos = ref []

let beneficial = ref false

let rec move_a_binder put_process b p =
  Terms.iproc_from_desc (
  match p.i_desc with 
    Nil -> 
      Settings.changed := true;
      Nil
  | Par(p1,p2) ->
      let r1 = Terms.refers_to_process b p1 in
      let r2 = Terms.refers_to_process b p2 in
      if r1 && r2 then
	raise Not_found
      else 
	begin
	  Settings.changed := true;
	  if r1 then
	    Par(move_a_binder put_process b p1,p2)
	  else if r2 then
	    Par(p1, move_a_binder put_process b p2)
	  else
	    Par(p1,p2)
	end
  | Repl(b',p) -> raise Not_found
  | Input((c,tl), pat, p) ->
      if (List.exists (Terms.refers_to b) tl) || (Terms.refers_to_pat b pat) then
	raise Not_found
      else
	Input((c,tl), pat, move_a_bindero put_process false b p))

and move_a_bindero put_process array_ref b p = 
  Terms.oproc_from_desc (
  match p.p_desc with
    Yield -> 
      if array_ref then
	put_process Yield
      else
	Yield
  | EventAbort f -> EventAbort f
  | Restr(b',p) -> 
      Settings.changed := true;
      Restr(b', move_a_bindero put_process array_ref b p)
  | Test(t,p1,p2) ->
      if Terms.refers_to b t then
	put_process (Test(t,p1,p2))
      else
	begin
	  Settings.changed:= true;
	  beneficial := true;
	  Test(t, move_a_bindero put_process array_ref b p1, move_a_bindero put_process array_ref b p2)
	end
  | Find(l0,p,find_info) ->
      if List.exists (fun (bl, def_list, t, _) ->
	(List.exists (Terms.refers_to_br b) def_list) ||
	Terms.refers_to b t) l0 then
	put_process (Find(l0,p,find_info))
      else
	begin
	  Settings.changed := true;
	  beneficial := true;
	  Find(List.map (fun (bl, def_list, t, p1) ->
	    (bl, def_list, t, 
	     move_a_bindero put_process array_ref b p1)) l0,
	       move_a_bindero put_process array_ref b p, find_info)
	end
  | Output((c,tl),t2,p) ->
      if (List.exists (Terms.refers_to b) tl) || (Terms.refers_to b t2) || array_ref then
	put_process (Output((c,tl),t2,p))
      else
	begin
	  try
	    let p' = move_a_binder put_process b p in
	    Settings.changed := true;
	    Output((c,tl), t2, p')
	  with Not_found ->
	    put_process (Output((c,tl),t2,p))
	end
  | Let(pat, t, p1, p2) ->
      if (Terms.refers_to b t) || (Terms.refers_to_pat b pat) then
	put_process (Let(pat, t, p1, p2))
      else
	begin
	  Settings.changed := true;
	  match pat with
	    PatVar _ -> 
	      Let(pat, t, move_a_bindero put_process array_ref b p1, Terms.oproc_from_desc Yield)
	  | _ -> 
	      beneficial := true;
	      Let(pat, t, move_a_bindero put_process array_ref b p1, 
		  move_a_bindero put_process array_ref b p2)
	end
  | EventP(t,p) ->
      if Terms.refers_to b t then
	put_process (EventP(t,p))
      else
	begin
	  Settings.changed := true;
	  EventP(t, move_a_bindero put_process array_ref b p)
	end
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  )

let rec move_a_let (b,t0) p = 
  Terms.iproc_from_desc (
  match p.i_desc with
    Nil -> 
      Settings.changed := true;
      Nil
  | Par(p1,p2) ->
      let r1 = Terms.refers_to_process b p1 in
      let r2 = Terms.refers_to_process b p2 in
      if r1 && r2 then
	raise Not_found
      else 
	begin
	  Settings.changed := true;
	  if r1 then
	    Par(move_a_let (b,t0) p1,p2)
	  else if r2 then
	    Par(p1, move_a_let (b,t0) p2)
	  else
	    Par(p1,p2)
	end
  | Repl(b',p) -> raise Not_found
  | Input((c,tl), pat, p) ->
      if (List.exists (Terms.refers_to b) tl) || (Terms.refers_to_pat b pat) then
	raise Not_found
      else
	Input((c,tl), pat, move_a_leto (b,t0) p)
  )

and move_a_leto (b,t0) p =
  Terms.oproc_from_desc (
  match p.p_desc with
    Yield -> Yield
  | EventAbort f -> EventAbort f
  | Restr(b',p) -> 
      Settings.changed := true;
      Restr(b', move_a_leto (b,t0) p)
  | Test(t,p1,p2) ->
      let r1 = Terms.refers_to_oprocess b p1 in
      let r2 = Terms.refers_to_oprocess b p2 in
      if (Terms.refers_to b t) || (r1 && r2) then
	Let(PatVar b, t0, Terms.oproc_from_desc (Test(t,p1,p2)), Terms.oproc_from_desc Yield)
      else
	begin
	  Settings.changed:= true;
	  beneficial := true;
	  Test(t, (if r1 then move_a_leto (b,t0) p1 else p1), 
	          (if r2 then move_a_leto (b,t0) p2 else p2))
	end
  | Find(l0,p,find_info) ->
      let rl = List.map (fun (bl, def_list, t, p1) ->
	Terms.refers_to_oprocess b p1) l0
      in
      let r2 = Terms.refers_to_oprocess b p in
      let count_ref = ref 0 in
      List.iter (fun b -> if b then incr count_ref) rl;
      if r2 then incr count_ref;
      if List.exists (fun (bl, def_list, t, _) ->
	(List.exists (Terms.refers_to_br b) def_list) ||
	Terms.refers_to b t) l0 || (!count_ref) > 1 then
	Let(PatVar b, t0, Terms.oproc_from_desc (Find(l0,p,find_info)), Terms.oproc_from_desc Yield)
      else
	begin
	  Settings.changed := true;
	  beneficial := true;
	  Find(List.map2 (fun (bl, def_list, t, p1) r1 ->
	    (bl, def_list, t, 
	     if r1 then move_a_leto (b,t0) p1 else p1)) l0 rl,
	       (if r2 then move_a_leto (b,t0) p else p), find_info)
	end
  | Output((c,tl),t2,p) ->
      if (List.exists (Terms.refers_to b) tl) || (Terms.refers_to b t2) then
	Let(PatVar b, t0, Terms.oproc_from_desc (Output((c,tl),t2,p)), Terms.oproc_from_desc Yield)
      else
	begin
	  try
	    let p' = move_a_let (b,t0) p in
	    Settings.changed := true;
	    Output((c,tl), t2, p')
	  with Not_found ->
	    Let(PatVar b, t0, Terms.oproc_from_desc (Output((c,tl),t2,p)), Terms.oproc_from_desc Yield)
	end
  | Let(pat, t, p1, p2) ->
      let r1 = Terms.refers_to_oprocess b p1 in
      let r2 = Terms.refers_to_oprocess b p2 in
      if (Terms.refers_to b t) || (Terms.refers_to_pat b pat) || (r1 && r2) then
	Let(PatVar b, t0, Terms.oproc_from_desc (Let(pat, t, p1, p2)), Terms.oproc_from_desc Yield)
      else
	begin
	  Settings.changed := true;
	  match pat with
	    PatVar _ -> 
	      Let(pat, t, (if r1 then move_a_leto (b,t0) p1 else p1), Terms.oproc_from_desc Yield)
	  | _ -> 
	      beneficial := true;
	      Let(pat, t, (if r1 then move_a_leto (b,t0) p1 else p1), 
		  (if r2 then move_a_leto (b,t0) p2 else p2))
	end
  | EventP(t,p) ->
      if Terms.refers_to b t then
	Let(PatVar b, t0, Terms.oproc_from_desc (EventP(t,p)), Terms.oproc_from_desc Yield)
      else
	begin
	  Settings.changed := true;
	  EventP(t, move_a_leto (b,t0) p)
	end
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  )


let do_move_new move_set array_ref b =
  match move_set with
    MAll | MNew -> true
  | MNoArrayRef | MNewNoArrayRef -> not array_ref
  | MLet -> false
  | MOneBinder b' -> b == b'

(* The result of do_move_let can be:
   0: do not move
   1: move but do not duplicate the let binding;
      this case happens only when b has no array accesses. 
   2: move, perhaps duplicating the let binding. *)

let do_move_let move_set array_ref b t =
  match move_set with
    MAll | MLet | MNoArrayRef -> 
      begin
	match t.t_desc with
	  FunApp(_,[]) -> 2 (* t is a constant; we allow duplicating its evaluation *)
	| _ -> if array_ref then 0 else 1
	(* Lets are moved only when there are no array references.
	   Moving them is interesting only when it reduces the cases in
           which the value is computed, which can never be done when there
	   are array references. *)
      end
  | MNew | MNewNoArrayRef -> 0
  | MOneBinder b' -> if b == b' then 2 else 0
      (* When the user instructs the move on the binder b, we perform
	 the move even if b has array references and/or we duplicate the let. *)

let rec move_new_let_rec move_set p =
  Terms.iproc_from_desc (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) -> Par(move_new_let_rec move_set p1,
		      move_new_let_rec move_set p2)
  | Repl(b,p) -> Repl(b,move_new_let_rec move_set p)
  | Input(t, pat, p) ->
      Input(t, pat, move_new_let_reco move_set p))

and move_new_let_reco move_set p =
  match p.p_desc with
    Yield -> Terms.oproc_from_desc Yield
  | EventAbort f -> Terms.oproc_from_desc (EventAbort f)
  | Restr(b,p) ->
      let array_ref = Terms.has_array_ref_q b in
      if (not (do_move_new move_set array_ref b)) then
	Terms.oproc_from_desc (Restr(b, move_new_let_reco move_set p))
      else
	let p' = move_new_let_reco move_set p in
	let tmp_changed = !Settings.changed in
	Settings.changed := false;
	beneficial := false;
	let p'' = move_a_bindero (fun p_desc -> Restr(b, Terms.oproc_from_desc p_desc)) array_ref b p' in
	if (!beneficial) || (match move_set with MOneBinder _ -> true | _ -> false) then
	  begin
	    Settings.changed := (!Settings.changed) || tmp_changed;
	    done_transfos := (DMoveNew b) :: (!done_transfos);
	    p''
	  end
	else
	  begin
	    (* Don't do a move all/noarrayref if it is not beneficial *)
	    Settings.changed := tmp_changed;
	    Terms.oproc_from_desc (Restr(b, p'))
	  end
  | Test(t,p1,p2) -> 
      Terms.oproc_from_desc 
	(Test(t, move_new_let_reco move_set p1,
	      move_new_let_reco move_set p2))
  | Find(l0,p,find_info) ->
      Terms.oproc_from_desc 
	(Find(List.map (fun (bl,def_list,t,p1) ->
	  (bl, def_list, t, move_new_let_reco move_set p1)) l0,
	   move_new_let_reco move_set p, find_info))
  | Output(t1,t2,p) ->
      Terms.oproc_from_desc (Output(t1,t2,move_new_let_rec move_set p))
  | Let(pat,t,p1,p2) ->
      begin
	match pat with
	  PatVar b ->
	    let array_ref = Terms.has_array_ref_q b in
	    let move_decision = do_move_let move_set array_ref b t in
	    if move_decision = 0 then
	      begin
		(* Do not move *)
		Terms.oproc_from_desc 
		  (Let(pat,t,move_new_let_reco move_set p1,
		       move_new_let_reco move_set p2))
	      end
	    else
	      begin
		let p1' = move_new_let_reco move_set p1 in
		let tmp_changed = !Settings.changed in
		Settings.changed := false;
		beneficial := false;
		let p1'' = 
		  if move_decision = 1 then 
		    (* Move the let, trying to evaluate it less often.
		       We never do that when b has array references.
		       In this case, the let binding is never duplicated. *)
		    move_a_leto (b,t) p1' 
		  else
		    (* Move the let, even if b has array references.
		       In this case, the let binding may be duplicated. *)
		    move_a_bindero (fun p_desc -> 
		      Let(pat, t, Terms.oproc_from_desc p_desc, Terms.oproc_from_desc Yield)) array_ref b p1'
		in
		if (!beneficial) || (match move_set with MOneBinder _ -> true | _ -> false) then
		  begin
		    Settings.changed := (!Settings.changed) || tmp_changed;
		       done_transfos := (DMoveLet b) :: (!done_transfos);
		       p1''
		  end
		else
		  begin
	        (* Don't do a move all/noarrayref if it is not beneficial *)
		    Settings.changed := tmp_changed;
		    Terms.oproc_from_desc (Let(pat, t, p1', Terms.oproc_from_desc Yield))
		  end
	      end
	| _ -> 
	    Terms.oproc_from_desc 
	      (Let(pat,t,move_new_let_reco move_set p1,
		move_new_let_reco move_set p2))
      end
  | EventP(t,p) ->
      Terms.oproc_from_desc (EventP(t, move_new_let_reco move_set p))
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

let move_new_let move_set g =
  done_transfos := [];
  Terms.array_ref_process g.proc;
  let r = move_new_let_rec move_set g.proc in
  Terms.cleanup_array_ref();
  let transfos = !done_transfos in
  done_transfos := [];
  ({ proc = r; game_number = -1; current_queries = g.current_queries}, [], transfos)

