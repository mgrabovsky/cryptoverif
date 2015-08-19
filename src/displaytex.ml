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

let nice_tex = ref true

let display_occurrences = ref false

let display_arrays = ref false

let times_to_display = ref []

let file = ref stdout

let print_string s =
  output_string (!file) s

let print_int i =
  print_string (string_of_int i)

let display_string s =
  for i = 0 to String.length s - 1 do
    match s.[i] with
      '\\' -> print_string "{\\textbackslash}"
    | '&' -> print_string "\\ensuremath{\\&}"
    | '{' -> print_string "\\ensuremath{\\{}"
    | '}' -> print_string "\\ensuremath{\\}}"
    | '_' -> print_string "{\\_}"
    | '^' -> print_string "{\\string^}"
    | '#' -> print_string "\\#"
    | '$' -> print_string "\\$"
    | '%' -> print_string "\\%"
    | '@' -> print_string "{\\string@}"
    | '~' -> print_string "{\\string~}"
    | '>' -> print_string "\\ensuremath{>}"
    | '<' -> print_string "\\ensuremath{<}"
    | c -> output_char (!file) c
  done  

let print_id prefix s suffix =
  print_string prefix;
  display_string s;
  print_string suffix

let rec display_list f = function
    [] -> ()
  | [a] -> f a
  | (a::l) -> f a; print_string ", ";
      display_list f l

let rec remove_common_prefix l1 l2 = match (l1,l2) with
  ({t_desc = ReplIndex ri1}::l1',ri2::l2') when ri1 == ri2 -> 
    remove_common_prefix l1' l2'
| _ -> l1

let remove_common_suffix l1 l2 =
  List.rev (remove_common_prefix (List.rev l1) (List.rev l2))

let display_table tbl = print_id "\\var{" tbl.tblname "}"

let display_type t =
  print_id "\\kwt{" t.tname "}"

let display_binder b =
  print_id "\\var{" b.sname "}";
  if (b.vname != 0) || (Display.ends_with_underscore_number b.sname) then 
    begin
      if !nice_tex then
	print_string ("_{" ^ (string_of_int b.vname) ^ "}")
      else
	print_string ("\\_" ^ (string_of_int b.vname))
    end

let display_repl_index b =
  print_id "\\var{" b.ri_sname "}";
  if (b.ri_vname != 0) || (Display.ends_with_underscore_number b.ri_sname) then 
    begin
      if !nice_tex then
	print_string ("_{" ^ (string_of_int b.ri_vname) ^ "}")
      else
	print_string ("\\_" ^ (string_of_int b.ri_vname))
    end

let rec display_var b tl =
      let tl = 
	if !display_arrays then tl else 
	remove_common_suffix tl b.args_at_creation 
      in
      display_binder b;
      if tl != [] then
	begin
	  print_string "[";
	  display_list display_term tl;
	  print_string "]"
	end

and display_binder_with_array b =
  display_binder b;
  if (!display_arrays) && (b.args_at_creation != []) then
    begin
      print_string "[";
      display_list display_repl_index b.args_at_creation;      
      print_string "]"
    end
  
and display_binder_with_type b =
  display_binder_with_array b;
  match b.btype.tcat with
    Interv n -> 
      print_id " \\leq \\kwp{" n.pname "}"
  | _ -> 
      print_id ": \\kwt{" b.btype.tname "}"

and display_repl_index_with_type b =
  display_repl_index b;
  print_id " \\leq \\kwp{" (Terms.param_from_type b.ri_type).pname "}"

and display_findcond (def_list, t1) =
  let cond_printed = ref false in
  if def_list != [] then
    begin
      print_string "\\kw{defined}(";
      display_list (fun (b,tl) -> display_var b tl) def_list;
      print_string ")";
      cond_printed := true
    end;
  if !cond_printed then
    begin
      if not (Terms.is_true t1) then
	begin
	  print_string (if !nice_tex then "\\wedge " else "\\ \\&\\&\\ ");
	  display_term t1
	end
    end
  else
    display_term t1

and display_term t = 
  if !display_occurrences then
    begin
      print_string "\\{";
      print_string (string_of_int t.t_occ);
      print_string "\\}"
    end;
  match t.t_desc with
    Var(b,tl) -> display_var b tl
  | ReplIndex b -> display_repl_index b
  | FunApp(f,l) ->
      begin
	match f.f_cat with
	  Std | Tuple | Event | LetFunTerm _ -> 
	    print_id "\\kwf{" f.f_name "}";
	    (* Event functions have replication indexes added at first argument
               Do not display it *)
	    let l = if f.f_cat == Event then List.tl l else l in
	    if (l != []) || (f.f_cat == Tuple) then
	      begin
		print_string "(";
		display_list display_term l;
		print_string ")"
	      end
	| LetEqual | Equal | Diff | ForAllDiff | Or | And ->
	    match l with
	      [t1;t2] -> 
		print_string "(";
		display_term t1;
		print_string (" " ^ (match f.f_name with
		  "&&" -> if !nice_tex then "\\wedge " else "\\ \\&\\&\\ "
		| "||" -> if !nice_tex then "\\vee " else "\\ \\|\\|\\ "
		| "=" -> " = "
		| "<>" -> " \neq "
		| _ -> f.f_name) ^ " ");
		display_term t2;
		print_string ")"
	    | _ -> Parsing_helper.internal_error "Infix operators need two arguments (display)"
      end
  | TestE(t1,t2,t3) ->
      print_string "\\kw{if}\\ ";
      display_term t1;
      print_string "\\ \\kw{then}\\ ";
      display_term t2;
      print_string "\\ \\kw{else}\\ ";
      display_term t3
  | FindE([([],def_list,t1,t2)],t3, find_info) ->
      print_string "\\kw{if}\\ ";
      display_findcond (def_list, t1);
      print_string "\\ \\kw{then}\\ ";
      display_term t2;
      print_string "\\ \\kw{else}\\ ";
      display_term t3
  | FindE(l0, t3, find_info) ->
      let first = ref true in
      print_string "\\kw{find}\\ ";
      if find_info = Unique then print_string "[\\kwf{unique}]\\ ";
      List.iter (fun (bl, def_list, t1, t2) ->
	if !first then
	  first := false
	else if !nice_tex then
	  print_string "\\ \\oplus\\ "
	else
	  print_string "\\ \\kw{orfind}\\ ";
	display_list (fun (b,b') -> display_binder_with_array b; print_string " = "; display_repl_index_with_type b') bl;
	print_string "\\ \\kw{suchthat}\\ ";
	display_findcond (def_list, t1);
	print_string "\\ \\kw{then}\\ ";
	display_term t2;
	print_string "$\\\\\n$"  (* Should align somehow... *)) l0;
      print_string "\\ \\kw{else}\\ ";
      display_term t3      
  | LetE(pat, t1, t2, topt) ->
      begin
	match pat with
	  PatVar b when (!Settings.front_end) == Settings.Oracles ->
	    display_binder_with_type b;
	    print_string " \\store ";
	    display_term t1;
	    print_string "; ";	    
	| _ ->
	    print_string "\\kw{let}\\ ";
	    display_pattern pat;
	    print_string " = ";
	    display_term t1;
	    print_string "\\ \\kw{in}\\ "
      end;
      display_term t2;
      begin
	match topt with
	  None -> ()
	| Some t3 ->
	    print_string "\\ \\kw{else}\\ ";
	    display_term t3      
      end
  | ResE(b,t) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  display_binder_with_array b;
	  print_id " \\getR \\kwt{" b.btype.tname "}"
	end
      else
	begin
	  print_string "\\kw{new}\\ ";
	  display_binder_with_type b
	end;
      print_string ";\\ ";
      display_term t
  | EventAbortE(f) ->
      print_string "\\kw{event\\string_abort}\\ ";
      print_id "\\kwf{" f.f_name "}"      

(* Patterns *)

and display_pattern = function
    PatVar b ->
      display_binder_with_type b
  | PatTuple (f,l) ->
      print_id "\\kwf{" f.f_name "}";
      print_string "(";
      display_list display_pattern l;
      print_string ")"
  | PatEqual t ->
      print_string "=";
      display_term t

(* Statements *)

let display_statement (bl, t) =
  print_string "$\\kw{forall}\\ ";
  display_list display_binder_with_type bl;
  print_string "; ";
  display_term t;
  print_string "$\\\\\n"

(* Equivalences *)

let display_action = function
    AFunApp f -> 
      begin
	match f.f_cat with
	  Tuple -> 
	    print_string "(";
	    display_list display_type (fst f.f_type);
	    print_string ")"	    
	| LetEqual | Equal | Diff | ForAllDiff ->
	    print_string (if f.f_cat = Diff then " \\neq " else ("\\kwf{" ^ f.f_name ^ "}"));
	    print_id " \\kwt{" (List.hd (fst f.f_type)).tname "}"
	| And -> print_string (if !nice_tex then "\\wedge " else "\\ \\&\\&\\ ")
	| Or -> print_string (if !nice_tex then "\\vee " else "\\ \\|\\|\\ ")
	| _ -> print_id "\\kwf{" f.f_name "}"
      end
  | APatFunApp f -> 
      begin
	match f.f_cat with
	  Tuple -> 
	    print_string "\\kw{let}\\ (";
	    display_list display_type (fst f.f_type);
	    print_string ")"
	| _ ->
	    print_id "\\kw{let}\\ \\kwf{" f.f_name "}"
      end
  | AReplIndex -> 
      if (!Settings.front_end) == Settings.Oracles then
	print_string "\\kw{foreach}"
      else
	print_string "!"
  | AArrayAccess n -> print_string ("[" ^ (string_of_int n) ^ "]")
  | ANew t -> 
      if (!Settings.front_end) == Settings.Oracles then
	print_string "\\getR "
      else
	print_string "\\kw{new}\\ ";
      display_type t
  | ANewChannel -> 
      if (!Settings.front_end) == Settings.Oracles then
	print_string "\\kw{newOracle}"
      else
	print_string "\\kw{newChannel}"
  | AIf -> print_string "\\kw{if}"
  | AFind n -> print_string ("\\kw{find}\\ " ^ (string_of_int n))
  | AOut (tl,t) -> 
      if (!Settings.front_end) == Settings.Oracles then
	Parsing_helper.internal_error "out action should not occur in oracles front-end";
      print_string "\\kw{out}\\ ";
      if tl != [] then
	begin
	  print_string "[";
	  display_list display_type tl;
	  print_string "]\\ "
	end;
      display_type t
  | AIn n -> 
      if (!Settings.front_end) == Settings.Oracles then
	Parsing_helper.internal_error "in action should not occur in oracles front-end";
      print_string ("\\kw{in}\\ " ^ (string_of_int n))

let rec display_proba level = function
    Proba (p,l) -> 
      print_id "\\var{" p.prname "}";
      if l != [] then
	begin
	  print_string "(";
	  display_list (display_proba 0) l;
	  print_string ")"
	end
  | Count p -> print_id "\\kwp{" p.pname "}"
  | OCount c -> print_id "\\#\\kwc{" c.cname "}"
  | Add(x,y) -> 
      if level > 1 then print_string "(";
      display_proba 1 x;
      print_string " + ";
      display_proba 1 y;
      if level > 1 then print_string ")"
  | Sub(x,y) -> 
      if level > 1 then print_string "(";
      display_proba 1 x;
      print_string " - ";
      display_proba 2 y;
      if level > 1 then print_string ")"
  | Max(l) -> 
      print_string "\\kw{max}(";
      display_list (display_proba 0) l;
      print_string ")"
  | Mul(x,y) ->
      if level > 3 then print_string "(";
      display_proba 3 x;
      print_string " \\times ";
      display_proba 3 y;
      if level > 3 then print_string ")"
  | Zero -> print_string "0"      
  | Cst n -> print_string (string_of_float n)
  | Div(x,y) ->
      if level > 3 then print_string "(";
      display_proba 3 x;
      print_string " / ";
      display_proba 4 y;
      if level > 3 then print_string ")"
  | Card t ->
      print_id "|\\kwt{" t.tname "}|"
  | AttTime ->
      print_string "\\kw{time}"
  | Time(g,t) ->
      print_string ("\\kw{time}(\\mathit{context\\ for\\ game}\\ " ^ (string_of_int g.game_number) ^ ")");
      begin
	try
	  ignore (List.assq g (!times_to_display))
	with Not_found -> 
	  times_to_display := (g,t)::(!times_to_display)
      end
  | ActTime(act, pl) ->
      print_string "\\kw{time}(";
      display_action act;
      if pl != [] then
	begin
	  print_string ", ";
	  display_list (display_proba 0) pl
	end;
      print_string ")"
  | Maxlength(g,t) ->
      print_string "\\kw{maxlength}(";
      if g.game_number>=0 then
	print_string ("\\mathit{game}\\ " ^ (string_of_int g.game_number) ^ ": ");
      display_term t;
      print_string ")"
  | TypeMaxlength(ty) ->
      print_id "\\kw{maxlength}(\\kwt{" ty.tname "})"
  | EpsFind ->
      print_string "\\kw{eps\\_find}"
  | EpsRand ty ->
      print_id "\\kw{eps\\_rand}(\\kwt{" ty.tname "})"
  | PColl1Rand ty ->
      print_id "\\kw{Pcoll1rand}(\\kwt{" ty.tname "})"
  | PColl2Rand ty ->
      print_id "\\kw{Pcoll2rand}(\\kwt{" ty.tname "})"
  | Length(f,pl) ->
      print_string "\\kw{length}(";
      begin
	match f.f_cat with
	  Tuple -> 
	    print_string "(";
	    display_list display_type (fst f.f_type);
	    print_string ")"	      
	| _ -> print_id "\\kwf{" f.f_name "}"
      end;
      if pl != [] then
	begin
	  print_string ", ";
	  display_list (display_proba 0) pl
	end;
      print_string ")"

let display_one_set = function
    SetProba r ->
      display_proba 0 r
  | SetEvent(f, g, _) ->
      print_id "\\Pr[\\kw{event}\\ \\kwf{" f.f_name "}\\textrm{ in game }";
      print_string (string_of_int g.game_number);
      print_string "]"

let rec display_set = function
    [] -> print_string "0"
  | [a] -> display_one_set a
  | a::l -> 
      display_one_set a;
      print_string " + ";
      display_set l
  

(* Only for the oracles front-end *)

let rec display_procasterm t = 
  if (!display_occurrences) || (List.memq t.t_occ (!Display.useful_occs)) then
    begin
      print_string "\\{";
      print_string (string_of_int t.t_occ);
      print_string "\\}"
    end;
  match t.t_desc with
    Var _ | FunApp _ ->
      print_string "\\kw{return}(";
      display_term t;
      print_string ")"
  | ReplIndex _ -> 
      Parsing_helper.internal_error "ReplIndex unexpected in display_procasterm"      
  | TestE(t1,t2,t3) ->
      print_string "\\kw{if}\\ ";
      display_term t1;
      print_string "\\ \\kw{then}\\ ";
      display_procasterm t2;
      print_string "\\ \\kw{else}\\ ";
      display_procasterm t3
  | FindE([([],def_list,t1,t2)],t3,find_info) ->
      print_string "\\kw{if}\\ ";
      display_findcond (def_list, t1);
      print_string "\\ \\kw{then}\\ ";
      display_procasterm t2;
      print_string "\\ \\kw{else}\\ ";
      display_procasterm t3
  | FindE(l0, t3, find_info) ->
      let first = ref true in
      print_string "\\kw{find}\\ ";
      if find_info = Unique then print_string "[\\kwf{unique}]\\ ";
      List.iter (fun (bl, def_list, t1, t2) ->
	if !first then
	  first := false
	else if !nice_tex then
	  print_string "\\ \\oplus\\ "
	else
	  print_string "\\ \\kw{orfind}\\ ";
	display_list (fun (b,b') -> display_binder_with_array b; print_string " = "; display_repl_index_with_type b') bl;
	print_string "\\ \\kw{suchthat}\\ ";
	display_findcond (def_list, t1);
	print_string "\\ \\kw{then}\\ ";
	display_procasterm t2;
	print_string "$\\\\\n$"  (* Should align somehow... *)) l0;
      print_string "\\ \\kw{else}\\ ";
      display_procasterm t3      
  | LetE(pat, t1, t2, topt) ->
      begin
	match pat with
	  PatVar b when (!Settings.front_end) == Settings.Oracles ->
	    display_binder_with_type b;
	    print_string " \\store ";
	    display_term t1;
	    print_string "; ";	    
	| _ ->
	    print_string "\\kw{let}\\ ";
	    display_pattern pat;
	    print_string " = ";
	    display_term t1;
	    print_string "\\ \\kw{in}\\ "
      end;
      display_procasterm t2;
      begin
	match topt with
	  None -> ()
	| Some t3 ->
	    print_string "\\ \\kw{else}\\ ";
	    display_procasterm t3      
      end
  | ResE(b,t) ->
      display_binder_with_array b;
      print_id " \\getR \\kwt{" b.btype.tname "};\\ ";
      display_procasterm t
  | EventAbortE(f) -> 
      print_string "\\kw{event\\string_abort}\\ ";
      print_id "\\kwf{" f.f_name "}"      
      

let rec display_fungroup indent = function
    ReplRestr(repl, restr, funlist) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  print_string "\\kw{foreach}\\ ";
	  display_repl_index_with_type repl;
	  print_string "\\ \\kw{do}\\ ";
	  List.iter (fun (b,opt) -> 
	    display_binder_with_array b;
	    print_id " \\getR \\kwt{" b.btype.tname "}"; 
	    if opt = Unchanged then
	      print_string "\\ [unchanged]"; 
	    print_string ";\\ ") restr
	end
      else if !nice_tex then
	begin
	  match repl.ri_type.tcat with
	    Interv n -> 
	      print_id "!^{\\kwp{" n.pname "}}\\ ";
	      List.iter (fun (b,opt) -> 
		print_string "\\kw{new}\\ ";
		display_binder_with_type b;
		if opt = Unchanged then
		  print_string "\\ [unchanged]"; 
		print_string ";\\ ") restr
	  | _ -> Parsing_helper.internal_error "Interval type expected"
	end
      else
	begin
	  print_string "!\\ ";
	  display_repl_index_with_type repl;
	  print_string "\\ ";
	  List.iter (fun (b,opt) -> 
	    print_string "\\kw{new}\\ ";
	    display_binder_with_type b;
	    if opt = Unchanged then
	      print_string "\\ [unchanged]"; 
	    print_string ";\\ ") restr
	end;
      begin
	match funlist with 
	  [f] -> 
	    display_fungroup indent f
	| _ -> 
	    print_string ("($\\\\\n$" ^ indent);
	    let first = ref true in
	    List.iter (fun f ->
	      if !first then
		first := false
	      else
		(if (!Settings.front_end) == Settings.Oracles then
		  print_string ("\\ |$\\\\\n$" ^ indent)
		else
		  print_string (",$\\\\\n$" ^ indent));
	      display_fungroup (indent ^ "\\quad ") f;
	      ) funlist;
	    print_string ")"
      end
  | Fun(ch, args, res, (priority, options)) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  print_id "\\kwc{" ch.cname "}(";
	  display_list display_binder_with_type args;
	  print_string ")";
	  if priority != 0 then
	    begin
	      print_string " [";
	      print_string (string_of_int priority);
	      print_string "]"
	    end;
	  begin
	    match options with
	      StdOpt -> ()
	    | UsefulChange -> print_string " [useful\\_change]"
	  end;
	  print_string " := ";
	  display_procasterm res
	end
      else if ch.cname = "@dummy_channel" then
	begin
	  print_string "(";
	  display_list display_binder_with_type args;
	  print_string ")";
	  if priority != 0 then
	    begin
	      print_string " [";
	      print_string (string_of_int priority);
	      print_string "]"
	    end;
	  print_string "\\ \\rightarrow\\ ";
	  display_term res
	end
      else
	begin
	  print_id "\\kwc{" ch.cname "}(";
	  display_list display_binder_with_type args;
	  print_string ")";
	  if priority != 0 then
	    begin
	      print_string " [";
	      print_string (string_of_int priority);
	      print_string "]"
	    end;
	  print_string " := ";
	  display_term res
	end

let display_eqmember l =
  display_list (fun (fg, mode) ->
    display_fungroup "\\quad  " fg;
    if mode = AllEquiv then print_string " [all]") l

let display_eqname = function
    NoName -> ()
  | CstName(s,_) -> print_id "\\kwc{" s "}\\ "
  | ParName((s,_),(p,_)) -> print_id "\\kwc{" s "}"; print_id "(\\kwf{" p "})\\ "

let display_equiv ((n,m1,m2,set,opt,opt2),_) =
  if !nice_tex then print_string "$" else print_string "$\\kw{equiv}\\ ";
  display_eqname n;
  display_eqmember m1;
  print_string "$\\\\\n$";
  if !nice_tex then
    begin
      print_string "\\approx_{";
      display_set set;
      print_string "}"
    end
  else
    begin
      print_string "\\Leftarrow(";
      display_set set;
      print_string ")\\Rightarrow"
    end;
  begin
    match opt, opt2 with
      StdEqopt, Decisional -> ()
    | PrioEqopt n, Decisional -> print_string ("\\ [" ^ (string_of_int n) ^ "]")
    | ManualEqopt, Decisional -> print_string "\\ [manual]"
    | StdEqopt, Computational -> print_string "\\ [computational]"
    | PrioEqopt n, Computational -> print_string ("\\ [" ^ (string_of_int n) ^ "]\\ [computational]")
    | ManualEqopt, Computational -> print_string "\\ [manual, computational]"
  end;
  print_string "$\\\\\n$";
  if not (!nice_tex) then print_string "\\phantom{\\kw{equiv}}\\ ";
  display_eqmember m2;
  print_string "$\\\\\n"

let display_equiv_with_name (((n,_,_,_,_,_),_) as eq) =
  match n with
    NoName -> display_equiv eq
  | _ -> print_string "$"; display_eqname n; print_string "$"

(* Processes *)

let display_channel c tl =
  print_id "\\kwc{" c.cname "}";
  if tl != [] then
    begin
      print_string "[";
      display_list display_term tl;
      print_string "]"
    end
  
let rec split_par p = 
  match p.i_desc with
    Par(p1,p2) -> (split_par p1) @ (split_par p2)
  | _ -> [p]

let rec may_have_elseo p = 
  match p.p_desc with
    Yield | EventAbort _ -> false
  | Test _ | Find _ | Let _ | Get _ -> true
  | Restr(_,p) | EventP(_,p) | Insert(_,_,p) -> may_have_elseo p
  | Output(_,_,p) -> may_have_else p

and may_have_else p = 
  match p.i_desc with
    Nil | Par _ -> false (* Par always introduces parentheses; whatever
	there is inside will be surrounded by these parentheses so does not
	need further parentheses *)
  | Repl(_,p) -> may_have_else p
  | Input(_,_,p) -> may_have_elseo p

let occ_space() =
  print_string "\\>$"

let rec display_process indent p = 
  if (!display_occurrences) || (List.memq p.i_occ (!Display.useful_occs)) then
    begin
      print_string "\\>\\{";
      print_string (string_of_int p.i_occ);
      print_string "\\}\\'$"
    end
  else
    occ_space();
  match p.i_desc with
    Nil -> 
      print_string (indent ^ "0$\\\\\n")
  | Par _ ->
      let pl = split_par p in
      print_string (indent ^ "($\\\\\n");
      let first = ref true in
      List.iter (fun pi ->
	if !first then first := false else 
	begin
	  occ_space();
	  print_string (indent ^ ") \\mid ($\\\\\n");
	end;
	display_process (indent ^ "\\quad ") pi) pl;
      occ_space();
      print_string (indent ^ ")$\\\\\n")	  
  | Repl(b,p) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  print_string (indent ^ "\\kw{foreach}\\ ");
	  display_repl_index_with_type b;
	  print_string "\\ \\kw{do}$\\\\\n"
	end
      else if !nice_tex then
	begin
	  print_string (indent ^ "!^{");
	  display_repl_index_with_type b;
	  print_string "}$\\\\\n"
	end
      else
	begin
	  print_string (indent ^ "!\\ ");
	  display_repl_index_with_type b;
	  print_string "$\\\\\n"
	end;
      display_process indent p
  | Input((c,tl),pat,p) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  print_id (indent ^ "\\kwc{") c.cname "}";
	  if (!display_arrays) && (tl != []) then
	    begin
	      print_string "[";
	      display_list display_term tl;
	      print_string "]"
	    end;
	  display_pattern pat;
	  print_string " :=$\\\\\n";
	  display_oprocess indent p
	end
      else if !nice_tex then
	begin
	  print_string (indent ^ "\\cinput{");
	  display_channel c tl;
	  print_string "}{";
	  begin
	    match pat with
	      PatTuple(f,l) when f.f_cat == Tuple ->
		display_list display_pattern l
	    | _ -> display_pattern pat
	  end;
	  print_string "}";
	  display_optoprocess indent p
	end
      else
	begin
	  print_string (indent ^ "\\kw{in}(");
	  display_channel c tl;
	  print_string ", ";
	  display_pattern pat;
	  print_string ")";
	  display_optoprocess indent p
	end

and display_oprocess indent p = 
  if (!display_occurrences) || (List.memq p.p_occ (!Display.useful_occs)) then
    begin
      print_string "\\>\\{";
      print_string (string_of_int p.p_occ);
      print_string "\\}\\'$"
    end
  else
    occ_space();
  match p.p_desc with
    Yield -> 
      if (!Settings.front_end) == Settings.Oracles then
	print_string (indent ^ "\\kw{end}$\\\\\n")
      else if !nice_tex then
	print_string (indent ^ "\\overline{0}$\\\\\n")
      else
	print_string (indent ^ "\\kw{yield}$\\\\\n")
  | EventAbort f -> 
      print_string (indent ^ "\\kw{event\\string_abort}\\ ");
      print_id "\\kwf{" f.f_name "}";
      print_string "$\\\\\n"
  | Restr(b,p) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  print_string indent;
	  display_binder_with_array b;
	  print_id " \\getR \\kwt{" b.btype.tname "}"
	end
      else
	begin
	  print_string (indent ^ "\\kw{new}\\ ");
	  display_binder_with_type b
	end;
      display_optoprocess indent p
  | Test(t,p1,p2) ->
      print_string (indent ^ "\\kw{if}\\ ");
      display_term t;
      print_string "\\ \\kw{then}$\\\\\n";
      if p2.p_desc = Yield then
	display_oprocess indent p1
      else
	begin
	  display_oprocess_paren indent p1;
	  occ_space();
	  print_string (indent ^ "\\kw{else}$\\\\\n");
	  display_oprocess (indent ^ "\\quad ") p2
	end
  | Find([([],def_list,t,p1)],p2,find_info) ->
      print_string (indent ^ "\\kw{if}\\ ");
      display_findcond (def_list,t);
      print_string "\\ \\kw{then}$\\\\\n";
      if p2.p_desc = Yield then
	display_oprocess indent p1
      else
	begin
	  display_oprocess_paren indent p1;
	  occ_space();
	  print_string (indent ^ "\\kw{else}$\\\\\n");
	  display_oprocess (indent ^ "\\quad ") p2
	end
  | Find(l0,p2,find_info) ->
      let first = ref true in
      let single_branch = (p2.p_desc = Yield) && (List.length l0 = 1) in
      print_string (indent ^ "\\kw{find}\\ ");
      if find_info = Unique then print_string "[\\kwf{unique}]\\ ";
      List.iter (fun (bl,def_list,t,p1) ->
	if !first then
	  first := false
	else 
	  begin
	    occ_space();
	    if !nice_tex then
	      print_string (indent ^ "\\oplus\\ ")
	    else
	      print_string (indent ^ "\\kw{orfind}\\ ")
	  end;
	display_list (fun (b,b') -> display_binder_with_array b; print_string " = "; display_repl_index_with_type b') bl;
	print_string "\\ \\kw{suchthat}\\ ";
	display_findcond (def_list,t);
	print_string "\\ \\kw{then}$\\\\\n";
	if single_branch then
	  display_oprocess indent p1
	else
	  display_oprocess_paren indent p1
	  ) l0;
      if p2.p_desc != Yield then
	begin
	  occ_space();
	  print_string (indent ^ "\\kw{else}$\\\\\n");
	  display_oprocess (indent ^ "\\quad ") p2
	end
  | Output((c,tl),t2,p) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  print_string (indent ^ "\\kw{return}");
	  display_term t2
	end
      else if !nice_tex then
	begin
	  print_string (indent ^ "\\coutput{");
	  display_channel c tl;
	  print_string "}{";
	  begin
	    match t2.t_desc with
	      FunApp(f, l) when f.f_cat == Tuple ->
		display_list display_term l
	    | _ -> display_term t2
	  end;
	  print_string "}"
	end
      else
	begin
	  print_string (indent ^ "\\kw{out}(");
	  display_channel c tl;
	  print_string ", ";
	  display_term t2;
	  print_string ")"
	end;
      display_optprocess indent p
  | Let(pat,t,p1,p2) ->
      begin
	match pat with
	  PatVar b when (!Settings.front_end) == Settings.Oracles ->
	    print_string indent;
	    display_binder_with_type b;
	    print_string " \\store ";
	    display_term t;
	    display_optoprocess indent p1
	| _ ->
	    print_string (indent ^ "\\kw{let}\\ ");
	    display_pattern pat;
	    print_string " = ";
	    display_term t;
	    if (p1.p_desc = Yield) && (p2.p_desc = Yield) then
	      print_string "$\\\\\n"
	    else
	      begin
		print_string "\\ \\kw{in}$\\\\\n";
		if p2.p_desc = Yield then
		  display_oprocess indent p1
		else
		  begin
		    display_oprocess_paren indent p1;
		    occ_space();
		    print_string (indent ^ "\\kw{else}$\\\\\n");
		    display_oprocess (indent ^ "\\quad ") p2
		  end
	      end
      end
  | EventP(t,p) ->
      print_string (indent ^ "\\kw{event}\\ ");
      display_term t;
      display_optoprocess indent p
  | Get (tbl,patl,topt,p1,p2) ->
      print_string (indent ^ "\\kw{get}\\ ");
      display_table tbl;
      print_string "\\ (";
      display_list display_pattern patl;
      print_string ")";
      (
        match topt with 
            None -> ();
          | Some t -> 
              print_string "\\ \\kw{suchthat}\\ ";
              display_term t
      );
      if (p1.p_desc = Yield) && (p2.p_desc = Yield) then
	print_string "$\\\\\n"
      else
	begin
	  print_string "\\ \\kw{in}$\\\\\n";
	  if p2.p_desc = Yield then
	    display_oprocess indent p1
	  else
	    begin
	      display_oprocess_paren indent p1;
	      occ_space();
	      print_string (indent ^ "\\kw{else}$\\\\\n");
	      display_oprocess (indent ^ "\\quad  ") p2
	    end
	end
  | Insert (tbl,tl,p) ->
      print_string (indent ^ "\\kw{insert}\\ ");
      display_table tbl;
      print_string "\\ ";
      display_list display_term tl;
      display_optoprocess indent p


and display_optprocess indent p =
  if p.i_desc = Nil then 
    print_string "$\\\\\n"
  else
    begin
      print_string ";$\\\\\n";
      display_process indent p
    end
      
and display_optoprocess indent p =
  if p.p_desc = Yield then 
    print_string "$\\\\\n"
  else
    begin
      print_string ";$\\\\\n";
      display_oprocess indent p
    end

and display_oprocess_paren indent p =
  if may_have_elseo p then
    begin
      occ_space();
      print_string (indent ^ "($\\\\\n");
      display_oprocess (indent ^ "\\quad ") p;
      occ_space();
      print_string (indent ^ ")$\\\\\n")
    end
  else
    display_oprocess (indent ^ "\\quad ") p

let display_process p =
  display_process "" p;
  print_string "\\\\\n"
	
(* Instructions *)

let display_rem_set = function
    All -> print_string "all\\ binders"
  | OneBinder b -> 
      print_string "binder $";
      display_binder b;
      print_string "$"
  | Minimal -> 
      print_string "useless"

let display_move_set = function
    MAll -> print_string "all\\ binders"
  | MNoArrayRef -> print_string "binders\\ without\\ array\\ references"
  | MNew -> print_string "all\\ new's"
  | MNewNoArrayRef -> print_string "new's\\ without\\ array\\ references"
  | MLet -> print_string "all\\ let's"
  | MOneBinder b -> 
      print_string "binder $";
      display_binder b;
      print_string "$"

let display_bl_assoc bl_assoc =
  display_list display_binder bl_assoc

let rec display_query1 = function
    [] -> Parsing_helper.internal_error "List should not be empty"
  | [b,t] -> 
      if b then print_string "\\kw{inj}:";
      display_term t
  | (b,t)::l ->
      if b then print_string "\\kw{inj}:";
      display_term t;
      print_string (if !nice_tex then " \\wedge " else "\\ \\&\\&\\ ");
      display_query1 l

let rec display_query2 = function
    QEvent(b,t) ->
      if b then print_string "\\kw{inj}:";
      display_term t
  | QTerm t ->
      display_term t
  | QOr(t1,t2) ->
      print_string "(";
      display_query2 t1;
      print_string (if !nice_tex then " \\vee " else "\\ \\|\\|\\ ");
      display_query2 t2;
      print_string ")"
  | QAnd(t1,t2) ->
      print_string "(";
      display_query2 t1;
      print_string (if !nice_tex then " \\wedge " else "\\ \\&\\&\\ ");
      display_query2 t2;
      print_string ")"

let display_query (q,g) = 
  match q with 
    AbsentQuery -> 
      if g.game_number <> 1 then
	print_string ("indistinguishability from game " ^ (string_of_int g.game_number))  
      else
	print_string "indistinguishability from the initial game"
  | _ ->
  begin
  match q with 
    QSecret1 b -> 
      print_string "one-session secrecy of $"; 
      display_binder b; 
      print_string "$"
  | QSecret b -> 
      print_string "secrecy of $"; 
      display_binder b; 
      print_string "$"
  | QEventQ(t1,t2) ->
      print_string "event $";
      display_query1 t1;
      print_string " \\Longrightarrow ";
      display_query2 t2;
      print_string "$"
  | AbsentQuery ->
      Parsing_helper.internal_error "AbsentQuery should have been handled"
  end;
  if g.game_number <> 1 then
    print_string (" in game " ^ (string_of_int g.game_number))  

let display_instruct = function
    ExpandIfFindGetInsert -> print_string "expand get, insert, if, let, find"
  | Simplify [] -> print_string "simplify"
  | Simplify l -> 
      print_string "simplify with collision elimination at ";
      display_list display_string l
  | GlobalDepAnal (b,l) ->
      print_string "global dependency analysis on $";
      display_binder b;
      print_string "$";
      if l != [] then
	begin
	  print_string " with collision elimination at ";
	  display_list print_string l
	end
  | MoveNewLet s -> print_string "move\\ "; display_move_set s
  | RemoveAssign r -> print_string "remove assignments of "; display_rem_set r
  | SArenaming b -> 
      print_string "SA rename $";
      display_binder b;
      print_string "$"
  | CryptoTransf(e, bl_assoc) -> 
      print_string "equivalence ";
      display_equiv_with_name e;
      if bl_assoc != [] then 
	begin
	  print_string "with $";
	  display_bl_assoc bl_assoc;
	  print_string "$"
	end
  | InsertEvent(s,occ) ->
      print_id "insert event $\\kwf{" s "}$";
      print_string (" at occurrence " ^ (string_of_int occ))
  | InsertInstruct(s,ext_s,occ,ext_o) ->
      print_string "insert instruction ";
      display_string s; 
      print_string (" at occurrence " ^ (string_of_int occ))
  | ReplaceTerm(s,ext_s,occ,ext_o) ->
      print_string ("replace term at occurrence " ^ (string_of_int occ) ^ " with ");
      display_string s
  | MergeArrays(bll, m) ->
      print_string "merge variables $";
      display_list (fun bl -> 
	print_string "("; 
	display_list (fun (b,_) -> display_binder b) bl;
	print_string ")") bll;
      print_string "$";
      begin
	match m with
	  MNoBranchVar -> print_string " (no branch variables)"
	| MCreateBranchVar -> ()
	| MCreateBranchVarAtProc _ -> print_string " (branch variables created at given processes)"
	| MCreateBranchVarAtTerm _ -> print_string " (branch variables created at given terms)"
      end
  | MergeBranches ->
      print_string "merge branches"
  | Proof ql -> 
      print_string "proof of ";
      display_list (fun (q, set) -> 
	display_query q; 
	if set != [] then
	  begin
	    print_string " up to probability $";
	    display_set set;
	    print_string "$"
	  end) ql

(* Explain probability formulas *)

let display_qevent = function
    Display.QEvent f,_ -> print_id "\\kwf{" f.f_name "}"
  | _ -> Parsing_helper.internal_error "QEvent expected"

let rec display_or_list = function
    [] -> ()
  | [a] -> display_qevent a
  | (a::l) -> display_qevent a; print_string " \\vee ";
      display_or_list l

let display_adv ql game = 
  let (ql_no_initq, ql_initq) = List.partition (function Display.InitQuery _,_ -> false | _ -> true) ql in
  match ql_initq with
    [Display.InitQuery q0,g0] ->
      print_string "\\mathsf{Adv}[\\mathrm{Game}\\ ";
      print_int game.game_number;
      print_string ": $";
      display_query (q0,g0);
      print_string "$";
      if ql_no_initq != [] then
	begin
	  print_string ", ";
	  display_or_list ql_no_initq
	end;
      print_string "]"
  | [] ->
      print_string "\\Pr[\\mathrm{Game}\\ ";
      print_int game.game_number;
      print_string ": ";
      display_or_list ql_no_initq;
      print_string "]"
  | _ -> Parsing_helper.internal_error "Bad query list in display_adv"

let rec evaluate_proba start_queries start_game above_proba ql pt =
  (* Sanity check: all elements of ql must occur in some edge in pt *)
  List.iter (fun qs -> 
    if not (List.exists (fun (_,_,_,ql_ref) -> 
      List.exists (Display.equal_qs qs) (!ql_ref)
	) pt.Display.pt_sons) then
      Parsing_helper.internal_error "Missing property in evaluate_proba"
	) ql;
  (* Sanity check: the ql_ref are disjoint *)
  let check_disjoint (_,_,_,ql_ref1) (_,_,_,ql_ref2) =
    if List.exists (fun qs1 -> List.exists (Display.equal_qs qs1) (!ql_ref2)) (!ql_ref1) then
      Parsing_helper.internal_error "ql_ref not disjoint"
  in
  let rec check_disjoint_l pt1 = function
      [] -> ()
    | (pt2::r) -> check_disjoint pt1 pt2; check_disjoint_l pt1 r
  in
  let rec check_disjoint_ll = function
      [] -> ()
    | (pt1::ptl) -> check_disjoint_l pt1 ptl; check_disjoint_ll ptl
  in
  check_disjoint_ll pt.Display.pt_sons;
  (* Take into account tree branching (several sons): split ql according to what
     each son proves *)
  match pt.Display.pt_sons with
    [(i,p,pt_son,ql_ref)] when (match i with Proof _ -> false | _ -> true) &&
       (List.for_all (function SetProba _ -> true | SetEvent _ -> false) p) ->
	 evaluate_proba start_queries start_game ((Display.double_if_needed ql p) @ above_proba) ql pt_son
  | _ -> 
      let ql_list = 
	List.map (fun (i,p,pt_son,ql_ref) ->
	  List.filter (fun qs -> List.exists (Display.equal_qs qs) ql) (!ql_ref)) pt.Display.pt_sons
      in
      print_string "$";
      display_adv start_queries start_game;
      print_string " \\leq ";
      display_proba 0 (Display.proba_from_set above_proba);
      List.iter (fun ql_i ->
	print_string " + ";
	display_adv ql_i pt.Display.pt_game) ql_list;
      print_string "$\\\\\n";
      above_proba @ 
  (List.concat (List.map (fun (i,p,pt_son,ql_ref) ->
    let ql' = List.filter (fun qs -> List.exists (Display.equal_qs qs) ql) (!ql_ref) in
    let rec compute_full_query_list = function
	[] -> ql'
      |	(SetProba _)::l -> compute_full_query_list l
      |	(SetEvent(f,g,_))::l -> (Display.QEvent f, g) :: (compute_full_query_list l)
    in
    (* One transformation can consist of an arbitrary syntactic or cryptographic
       transformation, that follows a series of event insertions (Shoup lemma).
       In practice, the transformation is either:
       - an event insertion alone
       - or a cryptographic transformation with an event insertion (DDH).
         The event insertion is indeed done before DDH.
       - or a transformation without event insertion. *)
    let ql'' = compute_full_query_list p in
    let proba_p = List.filter (function SetProba _ -> true | SetEvent _ -> false) p in
    match i with
      Proof pl ->
	(* The desired property is proved *)
	begin
	  match pl,ql' with
	    [q,_],[q'] -> 
	      let p = Display.double_if_needed ql' proba_p in
	      print_string "$";
	      display_adv ql' pt.Display.pt_game;
	      print_string " \\leq ";
	      display_proba 0 (Display.proba_from_set p);
	      print_string "$\\\\\n";
	      p
	  | _ -> Parsing_helper.internal_error "unexpected Proof element in proof tree"
	end
    | _ -> 
	(* We consider the whole set of queries ql' at once, 
	   and avoid counting several times the same events. *)
	let p = Display.double_if_needed ql' proba_p in
	if ql'' == ql' then
	  (* No event introduced *)
	  evaluate_proba ql' pt.Display.pt_game p ql'' pt_son
	else
	  begin
	    (* An event has been introduced, display its probability separately *)
	    print_string "$";
	    display_adv ql' pt.Display.pt_game;
	    print_string " \\leq ";
	    display_proba 0 (Display.proba_from_set p);
	    print_string " + ";
	    display_adv ql'' pt_son.Display.pt_game;
	    print_string "$\\\\\n";
	    p @ (evaluate_proba ql'' pt_son.Display.pt_game [] ql'' pt_son)
	  end
    ) pt.Display.pt_sons))

let compute_proba ((q0,g) as q) p s =
  let pt = Display.build_proof_tree q p s in
  (* display_proof_tree "" pt; *)
  let start_queries = [Display.InitQuery q0, g] in
  evaluate_proba start_queries g [] start_queries pt  



let display_pat_simp t =
  print_string (match t with 
    DEqTest -> " (equality test)\\\\\n"
  | DExpandTuple -> " (tuple expanded)\\\\\n"
  | DImpossibleTuple -> " (tuple matching always fails)\\\\\n")

let rec find_l def_list n = function
    [] -> print_string "[not found]"
  | (bl',def_list',t',p1')::l ->
      if def_list == def_list' then
	print_int n
      else
	find_l def_list (n+1) l

let get_finde_branch p (bl,def_list,t,p1) =
  match p.t_desc with
    FindE(l,_,_) -> find_l def_list 1 l
  | _ -> Parsing_helper.internal_error "Find expected in get_finde_branch"

let get_find_branch p (bl,def_list,t,p1) =
  match p.p_desc with
    Find(l,_,_) -> find_l def_list 1 l
  | _ -> Parsing_helper.internal_error "Find expected in get_find_branch"

let display_simplif_step = function
    SReplaceTerm(t,t') -> 
      print_string "\\qquad -- Replaced $";
      display_term t;
      print_string "$ with $";
      display_term t';
      print_string "$ at ";
      print_int t.t_occ;
      print_string "\\\\\n"
  | STestTrue(p) ->
      print_string "\\qquad -- Test at ";
      print_int p.p_occ;
      print_string " always true\\\\\n"
  | STestFalse(p) ->
      print_string "\\qquad -- Test at ";
      print_int p.p_occ;
      print_string " always false\\\\\n"
  | STestMerge(p) ->
      print_string "\\qquad -- Merge branches of test at ";
      print_int p.p_occ;
      print_string "\\\\\n"
  | STestOr(p) ->
      print_string ("\\qquad -- Expand $" ^ (if !nice_tex then "\\vee " else "\\|\\|") ^ "$ in test at ");
      print_int p.p_occ;
      print_string "\\\\\n"
  | STestETrue(t) ->
      print_string "\\qquad -- Test at ";
      print_int t.t_occ;
      print_string " always true\\\\\n" 
  | STestEFalse(t) ->
      print_string "\\qquad -- Test at ";
      print_int t.t_occ;
      print_string " always false\\\\\n" 
  | STestEMerge(t) ->
      print_string "\\qquad -- Merge branches of test at ";
      print_int t.t_occ;
      print_string "\\\\\n" 
  | STestEOr(t) ->
      print_string ("\\qquad -- Expand $" ^ (if !nice_tex then "\\vee " else "\\|\\|") ^ "$ in test at ");
      print_int t.t_occ;
      print_string "\\\\\n"
  | SFindBranchRemoved(p,br) -> 
      print_string "\\qquad -- Remove branch ";
      get_find_branch p br;
      print_string " in find at ";
      print_int p.p_occ;
      print_string "\\\\\n"
  | SFindSingleBranch(p,br) ->
      print_string "\\qquad -- A single branch always succeeds in find at ";
      print_int p.p_occ;
      print_string "\\\\\n"
  | SFindRemoved(p) ->
      print_string "\\qquad -- Find at ";
      print_int p.p_occ;
      print_string " removed (else branch kept if any)\\\\\n"
  | SFindElseRemoved(p) ->
      print_string "\\qquad -- Remove else branch of find at ";
      print_int p.p_occ;
      print_string "\\\\\n"
  | SFindBranchMerge(p, brl) ->
      begin
	match p.p_desc with
	  Find(l0,_,_) when List.length l0 = List.length brl ->
	    print_string "\\qquad -- Merge all branches of find at ";
	    print_int p.p_occ;
	    print_string "\\\\\n"
	| _ ->
	    print_string "\\qquad -- Merge branches ";
	    display_list (get_find_branch p) brl;
	    print_string " with else branch of find at ";
	    print_int p.p_occ;
	    print_string "\\\\\n"
      end
  | SFindDeflist(p, def_list, def_list') ->
      if def_list == [] then
	print_string "\\qquad -- Replaced an empty defined condition"
      else
	begin
	  print_string "\\qquad -- Replaced defined condition $";
	  display_list (fun (b,l) -> display_var b l) def_list;
	  print_string "$"
	end;
      print_string " with ";
      if def_list' == [] then
	print_string "an empty condition"
      else 
	begin
	  print_string "$";
	  display_list (fun (b,l) -> display_var b l) def_list';
	  print_string "$"
	end;
      print_string " in find at ";
      print_int p.p_occ;
      print_string "\\\\\n"
  | SFindinFindCondition(p, t) ->
      print_string "\\qquad -- Simplified find at ";
      print_int t.t_occ;
      print_string " in condition of find at ";
      print_int p.p_occ;
      print_string "\\\\\n"
  | SFindinFindBranch(p,p') ->
      print_string "\\qquad -- Simplified find at ";
      print_int p'.p_occ;
      print_string " in branch of find at ";
      print_int p.p_occ;
      print_string "\\\\\n"
  | SFindtoTest(p) ->
      print_string "\\qquad -- Transformed find at ";
      print_int p.p_occ;
      print_string " into a test\\\\\n"
  | SFindIndexKnown(p, br, subst) ->
      print_string "\\qquad -- In branch ";
      get_find_branch p br;
      print_string " of find at ";
      print_int p.p_occ;
      print_string ", substituting ";
      display_list (fun (b,t) -> 
	print_string "$"; display_binder b; print_string "$ with $";
        display_term t; print_string "$") subst;
      print_string "\\\\\n" 
  | SFindEBranchRemoved(t,br) -> 
      print_string "\\qquad -- Remove branch ";
      get_finde_branch t br;
      print_string " in find at ";
      print_int t.t_occ;
      print_string "\\\\\n"
  | SFindESingleBranch(t,br) ->
      print_string "\\qquad -- A single branch always succeeds in find at ";
      print_int t.t_occ;
      print_string "\\\\\n"
  | SFindERemoved(t) ->
      print_string "\\qquad -- Find at ";
      print_int t.t_occ;
      print_string " removed (else branch kept if any)\\\\\n"
  | SFindEElseRemoved(t) ->
      print_string "\\qquad -- Replace unused else branch of find at ";
      print_int t.t_occ;
      print_string " with a constant\\\\\n"
  | SFindEBranchMerge(t, brl) ->
      begin
	match t.t_desc with
	  FindE(l0,_,_) when List.length l0 = List.length brl ->
	    print_string "\\qquad -- Merge all branches of find at ";
	    print_int t.t_occ;
	    print_string "\\\\\n"
	| _ ->
	    print_string "\\qquad -- Merge branches ";
	    display_list (get_finde_branch t) brl;
	    print_string " with else branch of find at ";
	    print_int t.t_occ;
	    print_string "\\\\\n"
      end
  | SFindEDeflist(t, def_list, def_list') ->
      if def_list == [] then
	print_string "\\qquad -- Replaced an empty defined condition"
      else
	begin
	  print_string "\\qquad -- Replaced defined condition $";
	  display_list (fun (b,l) -> display_var b l) def_list;
	  print_string "$"
	end;
      print_string " with ";
      if def_list' == [] then
	print_string "an empty condition"
      else 
	begin
	  print_string "$";
	  display_list (fun (b,l) -> display_var b l) def_list';
	  print_string "$"
	end;
      print_string " in find at ";
      print_int t.t_occ;
      print_string "\\\\\n"
  | SFindinFindECondition(t, t') ->
      print_string "\\qquad -- Simplified find at ";
      print_int t'.t_occ;
      print_string " in condition of find at ";
      print_int t.t_occ;
      print_string "\\\\\n"
  | SFindinFindEBranch(t,t') ->
      print_string "\\qquad -- Simplified find at ";
      print_int t'.t_occ;
      print_string " in branch of find at ";
      print_int t.t_occ;
      print_string "\\\\\n"
  | SFindEtoTestE(t) ->
      print_string "\\qquad -- Transformed find at ";
      print_int t.t_occ;
      print_string " into a test\\\\\n"
  | SFindEIndexKnown(t, br, subst) ->
      print_string "\\qquad -- In branch ";
      get_finde_branch t br;
      print_string " of find at ";
      print_int t.t_occ;
      print_string ", substituting ";
      display_list (fun (b,t) -> 
	print_string "$"; display_binder b; print_string "$ with $";
        display_term t; print_string "$") subst;
      print_string "\\\\\n" 

  | SLetElseRemoved(p) ->
      print_string "\\qquad -- Remove else branch of let at ";
      print_int p.p_occ;
      print_string "\\\\\n"
  | SLetRemoved(p) ->
      print_string "\\qquad -- Remove let at ";
      print_int p.p_occ;
      print_string "\\\\\n"
  | SLetSimplifyPattern(p, pat, t) -> 
      print_string "\\qquad -- Simplify pattern $";
      display_pattern pat;
      print_string "$ at "; print_int p.p_occ;
      display_pat_simp t
  | SLetEElseRemoved(t) ->
      print_string "\\qquad -- Remove else branch of let at ";
      print_int t.t_occ;
      print_string "\\\\\n"
  | SLetERemoved(t) ->
      print_string "\\qquad -- Remove let at ";
      print_int t.t_occ;
      print_string "\\\\\n"
  | SLetESimplifyPattern(let_t, pat, t) -> 
      print_string "\\qquad -- Simplify pattern $";
      display_pattern pat;
      print_string "$ at "; print_int let_t.t_occ;
      display_pat_simp t

  | SResRemoved(p) ->
      print_string "\\qquad -- Remove random number generation at ";
      print_int p.p_occ;      
      print_string "\\\\\n"
  | SResToAssign(p) ->
      print_string "\\qquad -- Transform unused random number generation at ";
      print_int p.p_occ;      
      print_string " into constant assignment";
      print_string "\\\\\n"
  | SResERemoved(t) ->
      print_string "\\qquad -- Remove random number generation at ";
      print_int t.t_occ;
      print_string "\\\\\n"
  | SResEToAssign(t) ->
      print_string "\\qquad -- Transform unused random number generation at ";
      print_int t.t_occ;      
      print_string " into constant assignment";
      print_string "\\\\\n"

let display_detailed_ins = function
    DExpandGetInsert(t) -> 
      print_string "\\quad -- Expand get/insert for table $";
      display_table t;
      print_string "$\\\\\n"
  | DExpandIfFind ->
      print_string "\\quad -- Expand if/find/let\\\\\n"
  | DSimplify(l) ->
      print_string "\\quad -- Simplification pass\\\\\n";
      List.iter display_simplif_step (List.rev l)
  | DGlobalDepAnal(b,coll_elim) ->
      print_string "\\quad -- Global dependency analysis on $";
      display_binder b;
      print_string "$";
      if coll_elim != [] then
	begin
	  print_string " with collision elimination at ";
	  display_list display_string coll_elim
	end;
      print_string "\\\\\n"
  | DLetSimplifyPattern(let_p, pat, t) ->
      print_string "\\quad -- Simplify pattern $";
      display_pattern pat;
      print_string "$ at "; print_int let_p.p_occ;
      display_pat_simp t
  | DLetESimplifyPattern(let_t, pat, t) ->
      print_string "\\quad -- Simplify pattern $";
      display_pattern pat;
      print_string "$ at "; print_int let_t.t_occ;
      display_pat_simp t
  | DRemoveAssign(b, def_ch, usage_ch) ->
      print_string "\\quad -- Remove assignments on $";
      display_binder b;
      print_string (
	match def_ch with
	  DRemoveDef -> "$ (definition removed, "
	| DKeepDefPoint -> "$ (definition point kept, "
	| DKeepDef -> "$ (definition kept, ");
      print_string (
        match usage_ch with
	  DRemoveAll -> "all usages removed)\\\\\n"
	| DRemoveNonArray -> "array references kept)\\\\\n")
  | DSArenaming(b, bl) ->
      print_string "\\quad -- Rename variable $";
      display_binder b;
      print_string "$ into $";
      display_list display_binder bl;
      print_string "$\\\\\n"
  | DMoveNew(b) ->
      print_string "\\quad -- Move random number generation $";
      display_binder b;
      print_string "$\\\\\n"
  | DMoveLet(b) ->
      print_string "\\quad -- Move assignment to $";
      display_binder b;
      print_string "$\\\\\n"      
  | DCryptoTransf(e, bl_assoc) ->
      print_string "\\quad -- Equivalence ";
      display_equiv_with_name e;
      if bl_assoc != [] then
	begin
	  print_string "with $";
	  display_bl_assoc bl_assoc;
	  print_string "$"
	end;
      print_string "\\\\\n"
  | DInsertEvent _  | DInsertInstruct _ 
  | DReplaceTerm _  | DMergeArrays _ ->
      (* Don't display anything since the detailed description is the
	 same as the high level one *)
      ()
  | DMergeBranches(p,l) ->
      begin
	match (p.p_desc, l) with
	  (Test _), _ ->
	    print_string "\\quad -- Merge branches of test at ";
	    print_int p.p_occ
	| (Let _), _ ->
	    print_string "\\quad -- Merge branches of let at ";
	    print_int p.p_occ
	| (Find(l0,_,_), l) when List.length l = List.length l0 + 1 ->
	    print_string "\\quad -- Merge all branches of find at ";
	    print_int p.p_occ	    
	| (Find _), p1::r ->
	    print_string "\\quad -- Merge branch(es) at ";
	    display_list (fun p2 -> print_int p2.p_occ) r;
	    print_string " with else branch of find at ";
	    print_int p.p_occ
	| _ -> Parsing_helper.internal_error "unexpected merge"
      end;
      print_string "\\\\\n"            
  | DMergeBranchesE(t,l) ->
      begin
	match (t.t_desc, l) with
	  (TestE _), _ ->
	    print_string "\\quad -- Merge branches of test at ";
	    print_int t.t_occ
	| (LetE _), _ ->
	    print_string "\\quad -- Merge branches of let at ";
	    print_int t.t_occ
	| (FindE(l0,_,_), l) when List.length l = List.length l0 + 1 ->
	    print_string "\\quad -- Merge all branches of find at ";
	    print_int t.t_occ	    
	| (FindE _), t1::r ->
	    print_string "\\quad -- Merge branch(es) at ";
	    display_list (fun t2 -> print_int t2.t_occ) r;
	    print_string " with else branch of find at ";
	    print_int t.t_occ
	| _ -> Parsing_helper.internal_error "unexpected merge"
      end;
      print_string "\\\\\n"      

let already_displayed = ref []

let rec display_state ins_next s =
  if List.memq s (!already_displayed) then
    begin
      print_string "===================== New branch =====================\n";
      print_string "Game "; 
      print_int s.game.game_number;
      print_string " [Already displayed]\n";
    end
  else
    begin
      already_displayed := s :: (!already_displayed);
      match s.prev_state with
	None -> 
	  print_string "Initial state\\\\\n";
	  print_string ("Game " ^ (string_of_int s.game.game_number) ^ " is\\\\\n");
	  Display.mark_occs ins_next;
	  display_process s.game.proc;
	  Display.useful_occs := []
      | Some (Proof ql, p, _, s') ->
	  display_state ins_next s';
	  print_string "\\\\\n";
	  List.iter (fun ((q,g), p') -> 
	    if p' != [] then
	      begin
		print_string "Proved ";
		display_query (q, s'.game);
		print_string " up to probability $";
		display_proba 0 (Display.proba_from_set_may_double (q, s'.game) p');
		print_string "$\\\\\n"
	      end
	    else
	      begin
		print_string "Proved ";
		display_query (q, s'.game);
		print_string "\\\\\n"
	      end
		) ql;
	  if p != [] then
	    Parsing_helper.internal_error "Proof step should have empty set of excluded traces"
      | Some (i,p,ins,s') ->
	  display_state ins s';
	  print_string "\\\\\nApplying ";
	  display_instruct i;
	  if p != [] then
	    begin
	      print_string " {}[probability $";
	      display_set p;
	      print_string "${}]{}"
	    end;
	  print_string "\\\\\n";
	  List.iter display_detailed_ins (List.rev ins);
	  print_string "yields\\\\\n\\\\\n";
	  print_string ("Game " ^ (string_of_int s.game.game_number) ^ " is\\\\\n");
	  Display.mark_occs ins_next;
	  display_process s.game.proc;
	  Display.useful_occs := []
    end

let display_state s =
  (* Display the proof tree *)
  times_to_display := [];
  already_displayed := [];
  let initial_queries = Display.get_initial_queries s in
  let states_needed_in_queries = Display.get_all_states_from_queries initial_queries in
  let states_to_display = Display.remove_duplicate_states [] (s::states_needed_in_queries) in
  (* Set a tab stop after the occurrence display *)
  print_string (String.make (Display.len_num (!Terms.max_occ) + 2) '0');
  print_string "\\=\\kill\n";
  List.iter (fun s -> display_state [] s) states_to_display;  

  (* Display the probabilities of proved queries *)
  List.iter (fun (q,poptref,_) ->
    match !poptref with
      None -> ()
    | Some(p,s') -> 
        let p'' = compute_proba q p s' in
        print_string "RESULT Proved ";
        display_query q;
	if p'' != [] then
	  begin
            print_string " up to probability $";
            display_proba 0 (Display.proba_from_set p'');
	    print_string "$"
	  end;
	print_string "\\\\\n"
    ) initial_queries;

  (* Display the runtimes *)
  List.iter (fun (g,t) ->
    print_string ("RESULT $\\kw{time}(\\mathit{context\\ for\\ game}\\ " ^ (string_of_int g.game_number) ^ ") = ");
    display_proba 0 t;
    print_string "$\\\\\n"
    ) (List.rev (!times_to_display));
  times_to_display := [];

  (* List the unproved queries *)
  let rest = List.filter (function (q, poptref,_) -> (!poptref) == None) initial_queries in
  let rest' = List.filter (function (AbsentQuery, _),_,_ -> false | _ -> true) rest in
  if rest = [] then
    print_string "All queries proved.\\\\\n"
  else if rest' != [] then
    begin
      print_string "RESULT Could not prove ";
      display_list (fun (q, _,_) -> display_query q) rest;
      print_string ".\\\\\n"
    end


let preamble = "
\\documentclass{article}
\\usepackage[hmargin=1in,vmargin=1in]{geometry}
\\newcommand{\\kw}[1]{\\mathbf{#1}}
\\newcommand{\\kwf}[1]{\\mathsf{#1}}
\\newcommand{\\var}[1]{\\mathit{#1}}
\\newcommand{\\kwt}[1]{\\mathit{#1}}
\\newcommand{\\kwp}[1]{\\mathit{#1}}
\\newcommand{\\kwc}[1]{\\mathit{#1}}
\\begin{document}
\\begin{tabbing}
"

let nice_tex_preamble = "
\\documentclass{article}
\\usepackage[hmargin=1in,vmargin=1in]{geometry}
\\newcommand{\\cinput}[2]{{#1}({#2})}
\\newcommand{\\coutput}[2]{\\overline{#1}\\langle{#2}\\rangle}
\\newcommand{\\kw}[1]{\\mathbf{#1}}
\\newcommand{\\kwf}[1]{\\mathsf{#1}}
\\newcommand{\\var}[1]{\\mathit{#1}}
\\newcommand{\\kwt}[1]{\\mathit{#1}}
\\newcommand{\\kwp}[1]{\\mathit{#1}}
\\newcommand{\\kwc}[1]{\\mathit{#1}}
\\begin{document}
\\begin{tabbing}
"

let oracles_preamble = "
\\documentclass{article}
\\usepackage[hmargin=1in,vmargin=1in]{geometry}
\\newcommand{\\store}{\\leftarrow}
\\newcommand{\\getR}{\\stackrel{R}{\\store}}
\\newcommand{\\kw}[1]{\\mathbf{#1}}
\\newcommand{\\kwf}[1]{\\mathsf{#1}}
\\newcommand{\\var}[1]{\\mathit{#1}}
\\newcommand{\\kwt}[1]{\\mathit{#1}}
\\newcommand{\\kwp}[1]{\\mathit{#1}}
\\newcommand{\\kwc}[1]{\\mathit{#1}}
\\begin{document}
\\begin{tabbing}
"

let postamble = "
\\end{tabbing}
\\end{document}
"

let start() = 
  begin
    try
      file := open_out (!Settings.tex_output)
    with Sys_error s ->
      Parsing_helper.user_error ("File error: " ^ s ^ "\n")
  end;
  if (!Settings.front_end) == Settings.Oracles then
    print_string oracles_preamble
  else if !nice_tex then
    print_string nice_tex_preamble
  else
    print_string preamble

let stop() =
  print_string postamble;
  close_out (!file)
