(*************************************************************
 *                                                           *
 *       Cryptographic protocol verifier                     *
 *                                                           *
 *       Bruno Blanchet and David Cadé                       *
 *                                                           *
 *       Copyright (C) ENS, CNRS, INRIA, 2005-2015           *
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
open Ptree
open Types
open Stringmap
open Parsing_helper
open Lexing

(*
Get the environment computed in syntax.ml/osyntax.ml.
=> Stringmap.env
One pass on the initial game p, to build a hash table that
maps strings to binders or to "FindCond" for variables
defined in the condition of find (finds are forbidden on
such variables). 
=> hash_binders
Also indicate whether there is an array ref. on the other variables.
=> array_ref, array_ref_def
*)

type hash_elem =
    FindCond (* Defined in a find condition *)
  | Std of binder
  | NoDef (* Occurs in a defined condition but is never defined; the defined condition will always be wrong *)

let hash_binders = Hashtbl.create 7

let add b =
  let s = Display.binder_to_string b in
  try 
    match Hashtbl.find hash_binders s with
      NoDef -> 
	Hashtbl.replace hash_binders s (Std b)
    | FindCond ->
	Parsing_helper.internal_error "Variable in find condition defined several times"
    | _ -> ()
  with Not_found -> 
    Hashtbl.add hash_binders s (Std b)

let add_find_cond b =
  let s = Display.binder_to_string b in
  try 
    match Hashtbl.find hash_binders s with
      NoDef -> 
	Hashtbl.replace hash_binders s FindCond
    | _ ->
	Parsing_helper.internal_error "Variable in find condition defined several times"
  with Not_found -> 
    Hashtbl.add hash_binders s FindCond

let add_nodef b =
  let s = Display.binder_to_string b in
  if not (Hashtbl.mem hash_binders s) then
    Hashtbl.add hash_binders s NoDef

let rec find_binders_br (b,l) =
  List.iter find_binders_term_def_list l;
  add_nodef b

and find_binders_term_def_list t =
  match t.t_desc with
    Var(b,l) -> 
      List.iter find_binders_term_def_list l;
      add_nodef b
  | FunApp(_,l) ->
      List.iter find_binders_term_def_list l
  | ReplIndex _ -> ()
  | _ -> 
      Parsing_helper.internal_error "if/let/find/new forbidden in def_list"

let rec find_binders_find_cond t =
  match t.t_desc with
    Var _ | FunApp _ | ReplIndex _ -> ()
  | TestE(t1,t2,t3) ->
      find_binders_find_cond t2;
      find_binders_find_cond t3
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	List.iter (fun (b,_) -> add_find_cond b) bl;
        List.iter find_binders_br def_list;
	find_binders_find_cond t1;
	find_binders_find_cond t2) l0;
      find_binders_find_cond t3
  | ResE(b,t) ->
      add_find_cond b;
      find_binders_find_cond t
  | EventAbortE _ ->
      Parsing_helper.internal_error "event_abort should not occur as term"
  | LetE(pat, t1, t2, topt) ->
      let pat_vars = Terms.vars_from_pat [] pat in
      List.iter add_find_cond pat_vars;
      find_binders_find_cond t2;
      match topt with
	None -> ()
      |	Some t3 -> find_binders_find_cond t3
            

let rec find_binders_rec p =
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      find_binders_rec p1;
      find_binders_rec p2
  | Repl(b,p) -> 
      find_binders_rec p
  | Input((c, tl),pat,p) ->
      let pat_vars = Terms.vars_from_pat [] pat in
      List.iter add pat_vars;
      find_binders_reco p

and find_binders_reco p =
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b,p) -> 
      add b;
      find_binders_reco p
  | Test(t,p1,p2) ->
      find_binders_reco p1;
      find_binders_reco p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list,t,p1) ->
	List.iter (fun (b,_) -> add b) bl;
        List.iter find_binders_br def_list;
	find_binders_find_cond t;
	find_binders_reco p1) l0;
      find_binders_reco p2
  | Output((c, tl),t2,p) ->
      find_binders_rec p
  | Let(pat, t, p1, p2) ->
      let pat_vars = Terms.vars_from_pat [] pat in
      List.iter add pat_vars;
      find_binders_reco p1;
      find_binders_reco p2
  | EventP(t,p) ->
      find_binders_reco p
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"


(*
One pass on the initial game up to the program point occ to
- compute cur_array (current replication indices)
- compute the list defined_refs of allowed variable references
- update the environment env with variables bound above occ.
When reaching occ, add the instruction defined by the string s.
In contrast to the initial game, only code that satisfies the
invariants is accepted:
- variables defined at several places are not renamed
- terms if/let/find/new are not expanded, so they are allowed only in
conditions of find

A new definition for an existing variable can be added only when there
is no array ref. on this variable. We have to check that the new definition
is in a different branch of if/let/find, under the same replications,
and of the same type. To check that, return at the point the set of defined
variables.
*)

let check_noninter d1 d2 =
  List.iter (fun b1 ->
    if List.memq b1 d2 then
      raise (Error("Same variable " ^ (Display.binder_to_string b1) ^ " defined twice", Parsing_helper.dummy_ext))
	) d1

let rec check_single_var l ext = 
  match l with
    [] -> ()
  | (a::r) -> 
      if List.memq a r then
	raise (Error("Variable " ^ (Display.binder_to_string a) ^ " defined several times in this pattern", ext));
      check_single_var r ext

let is_yield (p,_) =
  if p != PYield then 
    Parsing_helper.internal_error "Yield process expected"

let get_var find_cond env (s_b, ext_b) ty_opt cur_array =
  if find_cond then

  try 
    match StringMap.find s_b env with
      _ -> 
	raise (Error(s_b ^ " already defined, so cannot be redefined in a find condition", ext_b))
  with Not_found ->
    if Hashtbl.mem hash_binders s_b then
      raise (Error(s_b ^ " already defined, so cannot be redefined in a find condition", ext_b));
      (* Variable not already defined *)
    match ty_opt with
      None -> raise (Error("type needed for the declaration of " ^ s_b, ext_b));
    | Some ty ->
	let b = Terms.create_binder s_b 0 ty cur_array in
	Hashtbl.add hash_binders s_b FindCond;
	b

  else

  try 
    match StringMap.find s_b env with
      EVar b -> 
	if Terms.has_array_ref_q b then
	  raise (Error(s_b ^ " already defined and has array references or is used in queries", ext_b));
	begin
	  match ty_opt with
	    None -> ()
	  | Some ty ->
	      if ty != b.btype then
		raise (Error(s_b ^ " already defined with type " ^ b.btype.tname ^ ", so cannot be redefined with type " ^ ty.tname, ext_b))
	end;
	if not (Terms.equal_lists (==) b.args_at_creation cur_array) then
	  raise (Error(s_b ^ " already defined, but under different replications", ext_b));
	b
    | _ -> raise (Error(s_b ^ " already defined and not a variable", ext_b))
  with Not_found ->
    try
      match Hashtbl.find hash_binders s_b with
	FindCond -> raise (Error(s_b ^ " already defined in a find condition, so cannot have several definitions", ext_b))
      | NoDef -> raise (Error(s_b ^ " already exists and the fact that it is defined is tested", ext_b))
      | Std b ->
	  if Terms.has_array_ref_q b then
	    raise (Error(s_b ^ " already defined and has array references or is used in queries", ext_b));
	  begin
	    match ty_opt with
	      None -> ()
	    | Some ty ->
		if ty != b.btype then
		  raise (Error(s_b ^ " already defined with type " ^ b.btype.tname ^ ", so cannot be redefined with type " ^ ty.tname, ext_b))
	  end;
	  if not (Terms.equal_lists (==) b.args_at_creation cur_array) then
	    raise (Error(s_b ^ " already defined, but under different replications", ext_b));
	  b
    with Not_found ->
      (* Variable not already defined *)
      match ty_opt with
	None -> raise (Error("type needed for the declaration of " ^ s_b, ext_b));
      |	Some ty ->
	  let b = Terms.create_binder s_b 0 ty cur_array in
	  Hashtbl.add hash_binders s_b (Std b);
	  b

let check_type ext e t =
  if e.t_type != t then
    raise (Error("This expression has type " ^ e.t_type.tname ^ " but expects type " ^ t.tname, ext))

let check_bit_string_type ext t =
  match t.tcat with
    BitString -> ()
  | _ -> raise (Error("Some bitstring type expected", ext))

let rec check_type_list ext pel el tl =
  match (pel, el, tl) with
    [],[],[] -> ()
  | (pe::pel, e::el, t::tl) ->
      check_type (snd pe) e t;
      check_type_list ext pel el tl
  | _ ->
      raise (Error("Unexpected number of arguments", ext))

let rec check_array_type_list ext pel el cur_array creation_array =
  match (pel, el, creation_array) with
    [],[],[] -> []
  | [],[],_ -> 
      (* Allow incomplete array arguments. They are automatically
         completed with cur_array *)
      let n = (List.length cur_array) - (List.length creation_array) in
      if n < 0 then 
	raise (Error("Unexpected number of array specifiers", ext));
      let cur_array_rest = Terms.skip n cur_array in
      if List.for_all2 (==) cur_array_rest creation_array then
	List.map Terms.term_from_repl_index creation_array
      else
	raise (Error("Unexpected number of array specifiers", ext))
  | (pe::pel, e::el, t::tl) ->
      check_type (snd pe) e t.ri_type;
      e::(check_array_type_list ext pel el cur_array tl)
  | _ ->
      raise (Error("Unexpected number of array specifiers", ext))


let rec check_term defined_refs cur_array env = function
    PIdent (s, ext), ext2 ->
      begin
      try 
	match StringMap.find s env with
	  EVar(b) -> 
	    Terms.new_term b.btype ext2 (Var(b,List.map Terms.term_from_repl_index b.args_at_creation))
	| EReplIndex(b) ->
	    Terms.new_term b.ri_type ext2 (ReplIndex(b))
	| EFunc(f) -> 
	    if fst (f.f_type) = [] then
	      Terms.new_term (snd f.f_type) ext2 (FunApp(f, []))
	    else
	      raise (Error(s ^ " has no arguments but expects some", ext))
	| _ -> raise (Error(s ^ " should be a variable or a function", ext))
      with Not_found -> try
	match Hashtbl.find hash_binders s with
	  Std b -> 
	    let tl'' = check_array_type_list ext2 [] [] cur_array b.args_at_creation in 
	    begin
	      match defined_refs with
		None -> () (* Do not check whether the reference is defined;
			      useful when parsing def_list *)
	      |	Some defined_refs' ->
		  if not (Terms.mem_binderref (b,tl'') defined_refs') then
		    raise (Error("The definition of an out of scope reference should be guaranteed by a defined condition", ext));
	    end;
	    Terms.new_term b.btype ext2 (Var(b,tl''))
	| NoDef | FindCond ->
	    raise (Error(s ^ " is referenced outside its scope and is either\ndefined in a condition of find or never defined", ext))
      with Not_found ->
	raise (Error(s ^ " not defined", ext))
      end
  | PArray((s, ext), tl), ext2 ->
      let (b, tl'') = check_br defined_refs cur_array env ((s,ext),tl) in
      Terms.new_term b.btype ext2 (Var(b,tl''))
  | PFunApp((s,ext), tl),ext2 ->
      let tl' = List.map (check_term defined_refs cur_array env) tl in
      begin
      try 
	match StringMap.find s env with
	  EFunc(f) ->
	    check_type_list ext2 tl tl' (fst f.f_type);
	    Terms.new_term (snd f.f_type) ext2 (FunApp(f, tl'))
	| _ -> raise (Error(s ^ " should be a function", ext))
      with Not_found ->
	raise (Error(s ^ " not defined", ext))
      end
  | PTuple(tl), ext2 ->
      let tl' = List.map (check_term defined_refs cur_array env) tl in
      let f = Settings.get_tuple_fun (List.map (fun t -> t.t_type) tl') in
      check_type_list ext2 tl tl' (fst f.f_type);
      Terms.new_term (snd f.f_type) ext2 (FunApp(f, tl'))
  | (PTestE _ | PLetE _ | PFindE _), ext ->
      raise (Error("if/let/find should appear as terms only in conditions of find", ext))
  | PResE _, ext ->
      raise (Error("new should not appear as term", ext))
  | PEventAbortE _, ext ->
      raise (Error("event_abort should not appear as term", ext))
  | PEqual(t1,t2), ext ->
      let t1' = check_term defined_refs cur_array env t1 in
      let t2' = check_term defined_refs cur_array env t2 in
      if t1'.t_type != t2'.t_type then
	raise (Error("= expects expressions of the same type", ext));
      Terms.make_equal_ext ext t1' t2'
  | PDiff(t1,t2), ext ->
      let t1' = check_term defined_refs cur_array env t1 in
      let t2' = check_term defined_refs cur_array env t2 in
      if t1'.t_type != t2'.t_type then
	raise (Error("<> expects expressions of the same type", ext));
      Terms.make_diff_ext ext t1' t2'
  | PAnd(t1,t2), ext ->
      let t1' = check_term defined_refs cur_array env t1 in
      let t2' = check_term defined_refs cur_array env t2 in
      check_type (snd t1) t1' Settings.t_bool;
      check_type (snd t2) t2' Settings.t_bool;
      Terms.make_and_ext ext t1' t2'
  | POr(t1,t2), ext ->
      let t1' = check_term defined_refs cur_array env t1 in
      let t2' = check_term defined_refs cur_array env t2 in
      check_type (snd t1) t1' Settings.t_bool;
      check_type (snd t2) t2' Settings.t_bool;
      Terms.make_or_ext ext t1' t2'
  | PInjEvent _,ext -> 
      raise (Error("inj: allowed only in queries", ext))

and check_br defined_refs cur_array env ((s,ext), tl) =
  let tl' = List.map (check_term defined_refs cur_array env) tl in
  try
    match Hashtbl.find hash_binders s with
      Std b -> 
	let tl'' = check_array_type_list ext tl tl' cur_array b.args_at_creation in
	begin
	  match defined_refs with
	    None -> () (* Do not check whether the reference is defined;
			  useful when parsing def_list *)
	  | Some defined_refs' ->
	      if not (Terms.mem_binderref (b,tl'') defined_refs') then
		raise (Error("The definition of an array reference should be guaranteed by a defined condition", ext));
	end;
	(b,tl'')
    | NoDef | FindCond ->
	raise (Error(s ^ " is referenced in an array reference and is either\ndefined in a condition of find or never defined", ext))
  with Not_found ->
    raise (Error(s ^ " not defined", ext))

let rec check_pattern find_cond defined_refs cur_array env tyoptres = function
    PPatVar ((s1,ext1), tyopt), _ ->
      begin
	let tyopt =
	  match tyopt, tyoptres with
	    None, None -> None
	  | None, Some ty -> Some ty
	  | Some (s2, ext2), None -> 
	      let ty' = get_type env s2 ext2 in
	      begin
		match ty'.tcat with
		  Interv _ -> raise (Error("Cannot input a term of interval type", ext2))
	        (* This condition simplifies greatly the theory:
	           otherwise, one needs to compute which channels the adversary
	           knows... *)
		|	_ -> ()
	      end;
	      Some ty'
	  | Some (s2,ext2), Some ty ->
	      let ty' = get_type env s2 ext2 in
	      if ty != ty' then
		raise (Error("Pattern is declared of type " ^ ty'.tname ^ " and should be of type " ^ ty.tname, ext2));
	      Some ty
	in
	let b = get_var find_cond env (s1, ext1) tyopt cur_array in
	let env' = StringMap.add s1 (EVar b) env in
	(env', PatVar b)
      end
  | PPatTuple l, ext ->
      begin
	match tyoptres with
	  None -> ()
	| Some ty ->
	    if ty != Settings.t_bitstring then
	      raise (Error("A tuple pattern has type bitstring but is here used with type " ^ ty.tname, ext))
      end;
      let tl = List.map (fun _ -> None) l in
      let (env', l') = check_pattern_list find_cond defined_refs cur_array env tl l in
      let tl' = List.map Terms.get_type_for_pattern l' in
      (env', PatTuple(Settings.get_tuple_fun tl', l'))
  | PPatFunApp((s,ext),l), ext2 -> 
      begin
      try 
	match StringMap.find s env with
	  EFunc(f) ->
	    if (f.f_options land Settings.fopt_COMPOS) == 0 then
	      raise (Error("Only [compos] functions are allowed in patterns", ext));
	    begin
	      match tyoptres with
		None -> ()
	      |	Some ty ->
		  if ty != snd f.f_type then
		    raise (Error("Pattern returns type " ^ (snd f.f_type).tname ^ " and should be of type " ^ ty.tname, ext2))
	    end;
	    if List.length (fst f.f_type) != List.length l then
	      raise (Error("Function " ^ f.f_name ^ " expects " ^ 
			   (string_of_int (List.length (fst f.f_type))) ^ 
			   " arguments but is here applied to " ^  
			   (string_of_int (List.length l)) ^ "arguments", ext));
	    let (env', l') = check_pattern_list find_cond defined_refs cur_array env (List.map (fun t -> Some t) (fst f.f_type)) l in
	    (env', PatTuple(f, l'))
	| _ -> raise (Error(s ^ " should be a function", ext))
      with Not_found ->
	raise (Error(s ^ " not defined", ext))
      end
  | PPatEqual t, ext ->
      let t' = check_term (Some defined_refs) cur_array env t in
      begin
	match tyoptres with
	  None -> ()
	| Some ty ->
	    if t'.t_type != ty then
	      raise (Error("Pattern has type " ^ (t'.t_type).tname ^ " and should be of type " ^ ty.tname, ext))
      end;
      (env, PatEqual t')

and check_pattern_list find_cond defined_refs cur_array env lty l = 
  match lty, l with
    [], [] -> (env,[])
  | (ty::lty),(a::l) ->
      let env', l' = check_pattern_list find_cond defined_refs cur_array env lty l in
      let env'', a' = check_pattern find_cond defined_refs cur_array env' ty a in
      (env'', a'::l')
  | _ -> Parsing_helper.internal_error "Lists have different length in check_pattern_list"


let rec check_find_cond defined_refs cur_array env = function
    PTestE(t1, t2, t3), ext ->
      let t1' = check_term (Some defined_refs) cur_array env t1 in
      let t2' = check_find_cond defined_refs cur_array env t2 in
      let t3' = check_find_cond defined_refs cur_array env t3 in
      check_type (snd t1) t1' Settings.t_bool;
      if t2'.t_type != t3'.t_type then
	raise (Error("Both branches of a test should yield the same type", ext));
      Terms.new_term t2'.t_type ext (TestE(t1', t2', t3'))
  | PLetE(pat, t1, t2, topt), ext ->
      let t1' = check_term (Some defined_refs) cur_array env t1 in
      let (env', pat') = check_pattern true defined_refs cur_array env (Some t1'.t_type) pat in
      let def2 = Terms.vars_from_pat [] pat' in
      let defined_refs' = (List.map Terms.binderref_from_binder def2) @ defined_refs in
      let t2' = check_find_cond defined_refs' cur_array env' t2 in
      let topt' = 
	match topt, pat with
	  Some t3, _ -> Some (check_find_cond defined_refs cur_array env t3)
	| None, (PPatVar _, _) -> None
	| None, _ -> Parsing_helper.input_error "When a let in an expression has no else part, it must be of the form let x = M in M'" ext
      in
      begin
	match topt' with
	  None -> ()
	| Some t3' -> if t2'.t_type != t3'.t_type then
	    raise (Error("Both branches of a let should return the same type", ext))
      end;
      Terms.new_term t2'.t_type ext (LetE(pat', t1', t2', topt'))
  | PResE((s1,ext1),(s2,ext2),t), ext ->
      raise (Error("new should not appear as term", ext))
(*
      let ty = get_type env s2 ext2 in
      if ty.toptions land Settings.tyopt_CHOOSABLE == 0 then
	raise (Error("Cannot choose randomly a bitstring from " ^ ty.tname ^ " with uniform distribution", ext2));
      let b = get_var true env (s1, ext1) (Some ty) cur_array in
      let env' = StringMap.add s1 (EVar b) env in
      let t' = check_find_cond defined_refs cur_array env' t in
      Terms.new_term t'.t_type ext (ResE(b, t'))
*)
  | PEventAbortE _, ext ->
      raise (Error("event_abort should not appear as term", ext))
  | PFindE(l0,t3,opt), ext ->
      if opt != [] then
	Parsing_helper.input_error "Options are not allowed for find in manually inserted instructions, because I cannot check that they are correct." ext;
      let rec add env = function
	  [] -> (env,[])
	| ((s1,ext1),(s2,ext2))::bl ->
	    let p = get_param env s2 ext2 in
	    let b = get_var true env (s1,ext1) (Some (Terms.type_for_param p)) cur_array in
	    let env' = StringMap.add s1 (EVar b) env in
	    let (env'',bl') = add env' bl in
	    if List.memq b bl' then
	      raise (Error("Variable " ^ (Display.binder_to_string b) ^ " defined several times in the same find", ext1));
	    (env'',b::bl')
      in
      let rec add_ri env = function
	  [] -> (env,[])
	| ((s1,ext1),(s2,ext2))::bl ->
	    let p = get_param env s2 ext2 in
	    let b = Terms.create_repl_index s1 (Terms.new_vname()) (Terms.type_for_param p) in
	    let env' = StringMap.add s1 (EReplIndex b) env in
	    let (env'',bl') = add_ri env' bl in
	    (env'',b::bl')
      in
      let t3' = check_find_cond defined_refs cur_array env t3 in
      let l0' = List.map (fun (_,bl,def_list,t1,t2) ->
	let (env', bl') = add env bl in
	let (env'', bl'') = add_ri env bl in
	let def_list' = List.map (check_br None (bl'' @ cur_array) env'') def_list in
	let bl_comb = List.combine bl' bl'' in
	let (defined_refs_t1, defined_refs_t2) = Terms.defined_refs_find bl_comb def_list' defined_refs in
	let t1' = check_find_cond defined_refs_t1 (bl'' @ cur_array) env'' t1 in
	let t2' = check_find_cond defined_refs_t2 cur_array env' t2 in
	check_type (snd t1) t1' Settings.t_bool;
	if t2'.t_type != t3'.t_type then
	  raise (Error("All branches of a if or find should return the same type", ext));
	(bl_comb, def_list', t1', t2')) l0 
      in
      Terms.new_term t3'.t_type ext (FindE(l0', t3', Nothing))
  | x -> check_term (Some defined_refs) cur_array env x


let rec insert_ins_now occ (p', def) (ins, ext) env cur_array =
  let defined_refs = 
    try 
      Facts.get_def_vars_at p'.p_facts 
    with Contradiction ->
      raise (Error("The occurrence " ^ (string_of_int occ) ^ " at which you are inserting an instruction is in fact unreachable", ext))
  in
  match ins with
    PRestr((s_b, ext_b), (s_ty, ext_ty), rest) ->
      is_yield rest;
      let ty = get_type env s_ty ext_ty in
      if ty.toptions land Settings.tyopt_CHOOSABLE == 0 then
	raise (Error("Cannot choose randomly a bitstring from " ^ ty.tname ^ " with uniform distribution", ext_ty));
      let b = get_var false env (s_b, ext_b) (Some ty) cur_array in
      check_noninter def [b];
      (Terms.oproc_from_desc (Restr(b, p')), b::def)
  | PEvent(t, rest) ->
      is_yield rest;
      let t' = check_term (Some defined_refs) cur_array env t in
      (Terms.oproc_from_desc (EventP(t', p')), def)
  | PTest(t, rest1, rest2) ->
      is_yield rest1;
      is_yield rest2;
      let t' = check_term (Some defined_refs) cur_array env t in
      (Terms.oproc_from_desc (Test(t', p', p')), def)
  | PLet(pat, t, rest1, rest2) ->
      is_yield rest1;
      is_yield rest2;
      let t' = check_term (Some defined_refs) cur_array env t in
      let (env', pat') = check_pattern false defined_refs cur_array env (Some t'.t_type) pat in
      let def2 = Terms.vars_from_pat [] pat' in
      check_single_var def2 (snd pat);
      check_noninter def def2;
      let def' = def2 @ def in
      begin
      match pat' with
	PatVar b ->
	  (Terms.oproc_from_desc (Let(pat', t', p', Terms.oproc_from_desc Yield)), def')
      |	_ ->
	  (Terms.oproc_from_desc (Let(pat', t', p', p')), def')
      end
  | PFind(l0, rest, opt) ->
      if opt != [] then
	Parsing_helper.input_error "Options are not allowed for find in manually inserted instructions, because I cannot check that they are correct." ext;
      is_yield rest;
      let def_accu = ref def in
      let rec add env = function
	  [] -> (env,[])
	| ((s1,ext1),(s2,ext2))::bl ->
	    let p = get_param env s2 ext2 in
	    let b = get_var false env (s1,ext1) (Some (Terms.type_for_param p)) cur_array in
	    let env' = StringMap.add s1 (EVar b) env in
	    let (env'',bl') = add env' bl in
	    if List.memq b bl' then
	      raise (Error("Variable " ^ (Display.binder_to_string b) ^ " defined several times in the same find", ext1));
	    (env'',b::bl')
      in
      let rec add_ri env = function
	  [] -> (env,[])
	| ((s1,ext1),(s2,ext2))::bl ->
	    let p = get_param env s2 ext2 in
	    let b = Terms.create_repl_index s1 (Terms.new_vname()) (Terms.type_for_param p) in
	    let env' = StringMap.add s1 (EReplIndex b) env in
	    let (env'',bl') = add_ri env' bl in
	    (env'',b::bl')
      in
      let l0' = List.map (fun (_,bl,def_list,t1,rest) ->
	is_yield rest;
	let (env', bl') = add env bl in
	let (env'', bl'') = add_ri env bl in
	let def_list' = List.map (check_br None (bl'' @ cur_array) env'') def_list in
	(* Compute the defined references in the condition t1 *)
	let accu = ref defined_refs in
	List.iter (Terms.close_def_subterm accu) def_list';
	let defined_refs_t1 = !accu in
	let t1' = check_find_cond defined_refs_t1 (bl'' @ cur_array) env'' t1 in
	check_type (snd t1) t1' Settings.t_bool;
	check_noninter bl' def;
	def_accu := Terms.unionq bl' (!def_accu);
	(List.combine bl' bl'', def_list', t1', p')) l0 
      in
      (Terms.oproc_from_desc (Find(l0', p', Nothing)), !def_accu)
  | _ ->
      Parsing_helper.internal_error "Unexpected inserted instruction"



let rec insert_ins count occ ins env cur_array p =
  let (p_desc', def) = 
  match p.i_desc with
    Nil -> (Nil, [])
  | Par(p1,p2) ->
      let (p1', def1) = insert_ins count occ ins env cur_array p1 in
      let (p2', def2) = insert_ins count occ ins env cur_array p2 in
      check_noninter def1 def2;
      (Par(p1',p2'), def1 @ def2)
  | Repl(b,p) ->
      let (p', def) = insert_ins count occ ins env (b::cur_array) p in
      (Repl(b,p'), def)
  | Input((c,tl),pat, p) ->
      let def2 = Terms.vars_from_pat [] pat in
      let env' = List.fold_left (fun env1 b -> StringMap.add (Display.binder_to_string b) (EVar b) env1) env def2 in
      let (p', def) = insert_inso count occ ins env' cur_array p in
      check_noninter def def2;
      (Input((c,tl),pat,p'), def @ def2)
  in
  (Terms.iproc_from_desc2 p p_desc', def)

and insert_inso count occ ins env cur_array p =
  let (p_desc', def) =
    match p.p_desc with
      Yield -> (Yield, [])
    | EventAbort f -> (EventAbort f, [])
    | Restr(b,p) ->
	let env' = StringMap.add (Display.binder_to_string b) (EVar b) env in
	let (p', def) = insert_inso count occ ins env' cur_array p in
	check_noninter def [b];
	(Restr(b,p'), b::def)
    | Test(t,p1,p2) ->
	let (p1', def1) = insert_inso count occ ins env cur_array p1 in
	let (p2', def2) = insert_inso count occ ins env cur_array p2 in
	(Test(t,p1',p2'), Terms.unionq def1 def2)
    | EventP(t,p) ->
	let (p', def) = insert_inso count occ ins env cur_array p in
	(EventP(t,p'), def)
    | Let(pat,t,p1,p2) ->
	let def2 = Terms.vars_from_pat [] pat in
	let env' = List.fold_left (fun env1 b -> StringMap.add (Display.binder_to_string b) (EVar b) env1) env def2 in
	let (p1', def1) = insert_inso count occ ins env' cur_array p1 in
	check_noninter def1 def2;
	let (p2', def3) = insert_inso count occ ins env cur_array p2 in
	(Let(pat,t,p1',p2'), Terms.unionq (def2 @ def1) def3)
    | Find(l0,p3,find_info) ->
	let (p3', def3) = insert_inso count occ ins env cur_array p3 in
	let accu = ref def3 in
	let l0' = List.map (fun (bl, def_list, t, p) ->
	  let vars = List.map fst bl in
	  let env' = List.fold_left (fun env1 b -> StringMap.add (Display.binder_to_string b) (EVar b) env1) env vars in	
	  (* I will check that the newly added definitions do not concern 
	     variables defined in the condition of find, so I do not need
	     to add the variables defined in t to def *)
	  let count_before = !count in
	  let (p', def) = insert_inso count occ ins env' cur_array p in
	  let count_after = !count in
	  let def_list' = 
	    if (count_before == 0) && (count_after == 1) then
	      let already_defined = Facts.get_def_vars_at p.p_facts in
	      let newly_defined = Facts.def_vars_from_defined (Facts.get_node p.p_facts) def_list in
	      Facts.update_def_list_process already_defined newly_defined bl def_list t p'
	    else
	      def_list
	  in
	  check_noninter def vars;
	  accu := Terms.unionq (vars @ def) (!accu);
	  (bl, def_list', t, p')
	  ) l0 
	in
	(Find(l0',p3',find_info), !accu)
    | Output((c,tl),t,p) ->
	let (p', def) = insert_ins count occ ins env cur_array p in
	(Output((c,tl),t,p'), def)
    | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  in
  let r = (Terms.oproc_from_desc2 p p_desc', def) in
  if p.p_occ == occ then
    begin
      incr count;
      insert_ins_now occ r ins env cur_array
    end
  else
    r

let insert_instruct occ ext_o s ext_s g =
  (* @ is not accepted in identifiers when parsing the initial file,
     but CryptoVerif creates variables with @, so I accept @ here. *)
  Parsing_helper.accept_arobase := true;
  let lexbuf = Lexing.from_string s in
  let ins = 
    try 
      if (!Settings.front_end) == Settings.Channels then 
	Parser.instruct Lexer.token lexbuf
      else
	Oparser.instruct Olexer.token lexbuf
    with
      Parsing.Parse_error -> raise (Error("Syntax error", combine_extent ext_s (extent lexbuf)))
    | Parsing_helper.IllegalCharacter -> raise (Error("Illegal character", combine_extent ext_s (extent lexbuf)))
    | Parsing_helper.IllegalEscape -> raise (Error("Illegal escape", combine_extent ext_s (extent lexbuf)))
    | Parsing_helper.UnterminatedString -> raise (Error("Unterminated string", combine_extent ext_s (extent lexbuf)))

  in
  Terms.array_ref_process g.proc;
  Terms.build_def_process None g.proc;
  Hashtbl.clear hash_binders;
  find_binders_rec g.proc;
  let count = ref 0 in
  let (p',_) = 
    try
      insert_ins count occ ins (!Stringmap.env) [] g.proc 
    with Error(mess, extent) ->
      Terms.cleanup_array_ref();
      Hashtbl.clear hash_binders;
      raise (Error(mess, combine_extent ext_s extent))
  in
  Terms.cleanup_array_ref();
  Hashtbl.clear hash_binders;
  if (!count) = 0 then 
    raise (Error("Occurrence " ^ (string_of_int occ) ^ " not found. You should use the command show_game occ to determine the desired occurrence.", ext_o))
  else if (!count > 1) then
    raise (Error("Occurrence " ^ (string_of_int occ) ^ " ambiguous. You should use the command show_game occ to determine the desired occurrence.", ext_o))
  else
    begin
      Settings.changed := true;
      let (g', proba, done_transfos) = Transf_auto_sa_rename.auto_sa_rename { proc = p'; game_number = -1; current_queries = g.current_queries } in
      (g', proba, done_transfos @ [DInsertInstruct(s, occ)])
    end
     
(**** Replace a term with an equal term ****)

type state_ty =
    RepToDo of int * Parsing_helper.extent * Ptree.term_e * Parsing_helper.extent 
  | RepDone of setf list * int * term * term * Parsing_helper.extent 

let whole_game = ref { proc = Terms.iproc_from_desc Nil; game_number = -1; current_queries = [] }

let rec replace_tt count env facts cur_array t =
  match !count with
    RepToDo (occ, ext_o, ins, ext_s) when occ == t.t_occ ->
      let defined_refs = 
	try 
	  Facts.get_def_vars_at t.t_facts 
	with Contradiction ->
	  raise (Error("The occurrence " ^ (string_of_int occ) ^ " at which you are replacing a term is in fact unreachable", ext_o))
      in
      let t' = check_term (Some defined_refs) cur_array env ins in
      if t'.t_type != t.t_type then
	raise (Error("You are trying to replace a term of type " ^ t.t_type.tname ^ " with a term of type " ^ t'.t_type.tname, ext_s));
      Simplify1.reset [] (!whole_game);
      let r = 
	try 
	  let facts' = Facts.get_facts_at t.t_facts in
	  let simp_facts = Terms.auto_cleanup (fun () -> Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) (facts'@facts)) in
	  let facts'' = 
	    if !Settings.elsefind_facts_in_replace then
	      Simplify1.get_facts_of_elsefind_facts (!whole_game) cur_array simp_facts defined_refs 
	    else
	      []
	  in
	  let simp_facts' = Terms.auto_cleanup (fun () -> Facts.simplif_add_list Facts.no_dependency_anal simp_facts facts'') in
	  Facts.check_equal t t' simp_facts' 
	with Contradiction ->
          (*   print_string "Got contradiction";
	       print_newline ();*)
          (* May happen when the program point of t is in fact unreachable
	     I say true anyway because the program point is unreachable. *)
	  true
      in
      if not r then
	raise (Error("I cannot prove that the term you want to put is equal to the term at " ^ (string_of_int occ), ext_s));
      count := RepDone(Simplify1.final_add_proba(), occ, t, t', ext_o);
      t'
  | RepDone(_,occ,_,_,ext_o) when occ == t.t_occ -> 
      raise (Error("Occurrence " ^ (string_of_int occ) ^ " ambiguous. You should use the command show_game occ to determine the desired occurrence.", ext_o))
  | _ -> 
      Terms.build_term2 t 
	(match t.t_desc with
	  Var(b,l) -> Var(b, List.map (replace_tt count env facts cur_array) l)
	| ReplIndex b -> ReplIndex b
	| FunApp(f,[t1;t2]) when f == Settings.f_and ->
	    (* This is correct because the replacement is done either in t1 or in t2,
	       but not in both! 
	       If the replacement is done in t2, we consider that the expression is
	       evaluated as t1 && t2, so that t2 is evaluated only when t1 holds.
	       If the replacement is done in t1, we consider that the expression is
	       evaluated as t2 && t1, so that t1 is evaluated only when t2 holds. *)
	  FunApp(f, [replace_tt count env (t2::facts) cur_array t1;
		 replace_tt count env (t1::facts) cur_array t2])
	| FunApp(f,[t1;t2]) when f == Settings.f_or ->
	    (* This is correct because the replacement is done either in t1 or in t2,
	       but not in both! 
	       If the replacement is done in t2, we consider that the expression is
	       evaluated as t1 || t2, so that t2 is evaluated only when t1 is false.
	       If the replacement is done in t1, we consider that the expression is
	       evaluated as t2 || t1, so that t1 is evaluated only when t2 is false. *)
	  FunApp(f, [replace_tt count env ((Terms.make_not t2)::facts) cur_array t1;
		 replace_tt count env ((Terms.make_not t1)::facts) cur_array t2])
	| FunApp(f,l) -> FunApp(f, List.map (replace_tt count env facts cur_array) l)
	| ResE _ | TestE _ | LetE _ | FindE _ | EventAbortE _ ->
	    Parsing_helper.internal_error "if/let/find/new/event_abort should have been expanded in replace_term")

let rec replace_tpat count env cur_array = function
    PatVar b -> PatVar b
  | PatTuple(f,l) -> PatTuple(f, List.map (replace_tpat count env cur_array) l)
  | PatEqual t -> PatEqual(replace_tt count env [] cur_array t)

and replace_tfind_cond count env cur_array t =
  match t.t_desc with
    ResE(b,p) ->
      let env' = StringMap.add (Display.binder_to_string b) (EVar b) env in
      Terms.build_term2 t (ResE(b, replace_tfind_cond count env' cur_array p))
  | EventAbortE _ ->
      Parsing_helper.internal_error "event_abort should not occur as term"
  | TestE(t1,t2,t3) ->
      let t2' = replace_tfind_cond count env cur_array t2 in
      let t3' = replace_tfind_cond count env cur_array t3 in
      let t1' = replace_tt count env [] cur_array t1 in
      Terms.build_term2 t (TestE(t1',t2',t3'))
  | LetE(pat,t1,t2,topt) ->
      let def2 = Terms.vars_from_pat [] pat in
      let env' = List.fold_left (fun env1 b -> StringMap.add (Display.binder_to_string b) (EVar b) env1) env def2 in
      let t2' = replace_tfind_cond count env' cur_array t2 in
      let topt' = 
	match topt with
	  None -> None
	| Some t3 -> Some (replace_tfind_cond count env cur_array t3)
      in
      let pat' = replace_tpat count env cur_array pat  in
      let t1' = replace_tt count env [] cur_array t1 in
      Terms.build_term2 t (LetE(pat',t1',t2',topt'))
  | FindE(l0,t3, find_info) ->
      let t3' = replace_tfind_cond count env cur_array t3 in
      let l0' = List.map (fun (bl, def_list, tc, p) ->
	let vars = List.map fst bl in
	let repl_indices = List.map snd bl in

	(* Compute the environment in the then branch p *)
	let env_p = List.fold_left (fun env1 b -> StringMap.add (Display.binder_to_string b) (EVar b) env1) env vars in	
	(* Compute the environment in the condition tc *)
	let env_tc = List.fold_left (fun env1 b -> StringMap.add (Display.repl_index_to_string b) (EReplIndex b) env1) env repl_indices in
	let count_before = !count in
	let p' = replace_tfind_cond count env_p cur_array p in
	let tc' = replace_tfind_cond count env_tc cur_array tc in
	let count_after = !count in
	(* Update def_list if needed *)
	let def_list' = 
	  match count_before, count_after with
	    RepToDo _, RepDone _ -> 
	      let already_defined = Facts.get_def_vars_at t.t_facts in
	      let newly_defined = Facts.def_vars_from_defined (Facts.get_node t.t_facts) def_list in
	      Facts.update_def_list_term already_defined newly_defined bl def_list tc' p'
	  | _ -> def_list
	in
	(bl, def_list', tc', p')
	  ) l0 
      in
      Terms.build_term2 t (FindE(l0',t3',find_info))
  | Var _ | FunApp _ | ReplIndex _ -> replace_tt count env [] cur_array t 

let rec replace_t count env cur_array p =
  let p_desc' =
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) ->
      Par(replace_t count env cur_array p1,
	  replace_t count env cur_array p2)
  | Repl(b,p) ->
      Repl(b, replace_t count env (b::cur_array) p)
  | Input((c,tl),pat, p) ->
      let def2 = Terms.vars_from_pat [] pat in
      let env' = List.fold_left (fun env1 b -> StringMap.add (Display.binder_to_string b) (EVar b) env1) env def2 in
      let p' = replace_to count env' cur_array p in
      let pat' = replace_tpat count env cur_array pat in
      let tl' = List.map (replace_tt count env [] cur_array) tl in
      Input((c,tl'),pat',p')
  in
  Terms.iproc_from_desc2 p p_desc'

and replace_to count env cur_array p =
  let p_desc' =
    match p.p_desc with
      Yield -> Yield
    | EventAbort f -> EventAbort f
    | Restr(b,p) ->
	let env' = StringMap.add (Display.binder_to_string b) (EVar b) env in
	Restr(b, replace_to count env' cur_array p)
    | Test(t,p1,p2) ->
	let p1' = replace_to count env cur_array p1 in
	let p2' = replace_to count env cur_array p2 in
	let t' = replace_tt count env [] cur_array t in
	Test(t',p1',p2')
    | EventP(t,p) ->
	let p' = replace_to count env cur_array p in
	let t' = replace_tt count env [] cur_array t in
	EventP(t',p')
    | Let(pat,t,p1,p2) ->
	let def2 = Terms.vars_from_pat [] pat in
	let env' = List.fold_left (fun env1 b -> StringMap.add (Display.binder_to_string b) (EVar b) env1) env def2 in
	let p1' = replace_to count env' cur_array p1 in
	let p2' = replace_to count env cur_array p2 in
	let pat' = replace_tpat count env cur_array pat  in
	let t' = replace_tt count env [] cur_array t in
	Let(pat',t',p1',p2')
    | Find(l0,p3,find_info) ->
	let p3' = replace_to count env cur_array p3 in
	let l0' = List.map (fun (bl, def_list, t, p1) ->
	  let vars = List.map fst bl in
	  let repl_indices = List.map snd bl in

	  (* Compute the environment in the then branch p1 *)
	  let env_p1 = List.fold_left (fun env1 b -> StringMap.add (Display.binder_to_string b) (EVar b) env1) env vars in	
	  (* Compute the environment in the condition t *)
	  let env_t = List.fold_left (fun env1 b -> StringMap.add (Display.repl_index_to_string b) (EReplIndex b) env1) env repl_indices in
	  let count_before = !count in
	  let p1' = replace_to count env_p1 cur_array p1 in
	  let t' = replace_tfind_cond count env_t cur_array t in
	  let count_after = !count in
	  (* Update def_list if needed *)
	  let def_list' = 
	    match count_before, count_after with
	      RepToDo _, RepDone _ ->
		let already_defined = Facts.get_def_vars_at p.p_facts in
		let newly_defined = Facts.def_vars_from_defined (Facts.get_node p.p_facts) def_list in
		Facts.update_def_list_process already_defined newly_defined bl def_list t' p1'
	    | _ -> def_list
	  in
	  (bl, def_list', t', p1')
	  ) l0 
	in
	Find(l0',p3',find_info)
    | Output((c,tl),t,p) ->
	let p' = replace_t count env cur_array p in
	let t' = replace_tt count env [] cur_array t in
	let tl' = List.map (replace_tt count env [] cur_array) tl in
	Output((c,tl'),t',p')
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  in
  Terms.oproc_from_desc2 p p_desc'

let replace_term occ ext_o s ext_s g =
  (* @ is not accepted in identifiers when parsing the initial file,
     but CryptoVerif creates variables with @, so I accept @ here. *)
  Parsing_helper.accept_arobase := true;
  let lexbuf = Lexing.from_string s in
  let rep_term = 
    try 
      if (!Settings.front_end) == Settings.Channels then 
	Parser.term Lexer.token lexbuf
      else
	Oparser.term Olexer.token lexbuf
    with
      Parsing.Parse_error -> raise (Error("Syntax error", combine_extent ext_s (extent lexbuf)))
    | Parsing_helper.IllegalCharacter -> raise (Error("Illegal character", combine_extent ext_s (extent lexbuf)))
    | Parsing_helper.IllegalEscape -> raise (Error("Illegal escape", combine_extent ext_s (extent lexbuf)))
    | Parsing_helper.UnterminatedString -> raise (Error("Unterminated string", combine_extent ext_s (extent lexbuf)))
  in
  Terms.array_ref_process g.proc;
  Terms.build_def_process None g.proc;
  Terms.build_compatible_defs g.proc;
  Hashtbl.clear hash_binders;
  find_binders_rec g.proc;
  whole_game := g;
  let count = ref (RepToDo (occ, ext_o, rep_term, ext_s)) in
  let p' = 
    try
      replace_t count (!Stringmap.env) [] g.proc 
    with Error(mess, extent) ->
      Terms.cleanup_array_ref();
      Hashtbl.clear hash_binders;
      Terms.empty_comp_process g.proc;
      raise (Error(mess, extent))
  in
  Terms.cleanup_array_ref();
  Hashtbl.clear hash_binders;
  Terms.empty_comp_process g.proc;
  match !count with
    RepToDo _ ->
      raise (Error("Occurrence " ^ (string_of_int occ) ^ " not found. You should use the command show_game occ to determine the desired occurrence.", ext_o))
  | RepDone(sets,_,t,t',_) ->
      Settings.changed := true;
      ({ proc = p'; game_number = -1; current_queries = g.current_queries  }, sets, [DReplaceTerm(t,t',occ)])
