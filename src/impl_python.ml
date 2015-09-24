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
open Types
open Implementation


(* This should have been in the standard library *)
let rec replicate (n:int) (x:'a) : 'a list =
  if n < 1 then []
  else x :: (replicate (n - 1) x)
let lines (str:string) : string list  = Str.split (Str.regexp "\n") str
let unlines (xs:string list) : string = String.concat "\n" xs
let indent_by (n:int) (str:string) : string =
  let ind = String.concat "" (replicate n "    ") in
  unlines (List.map (fun x -> ind^x) (lines str))
let indent : string -> string = indent_by 1

(* Helper functions for nicer output format *)
let func_call fname arg =
  if fname = "" then
    arg
  else
    fname^"("^arg^")"
let tuple_or_bare f = function
  | []  -> assert false
  | [x] -> f x
  | xs  -> "("^(string_list_sep ", " (List.map f xs))^")"


(*returns set of free and set of bound variables
  get_iprocess_bv returns the set of variables bound not under a replication
  The set of variables bound under a replication is stored in
  bound_vars_under_repl.
  The set of free variables is stored in free_vars. *)

(* returns the next oracles. b represents if the oracle is under replication (false) or not (true) *)

let rec get_next_oracles b p =
  match p.i_desc with
    | Nil -> []
    | Input((c,tl),pat,p) ->
        if b then
          let token = create_fresh_name "token_" in
          [(Some token,c.cname,pat,p)]
        else
          [(None,c.cname,pat,p)]
    | Par (p1,p2) ->
        (get_next_oracles b p1) @ (get_next_oracles b p2)
    | Repl(b,p) -> get_next_oracles false p


let term_tuple_types t =
  match !Settings.front_end with
    | Settings.Oracles ->
        (
          match t.t_desc with
            | FunApp(f,tl) when f.f_name = "" ->
                  List.map (fun t -> t.t_type) tl
            | _ -> Parsing_helper.internal_error "The output term must be a call to the function \"\""
        )
    | Settings.Channels ->
        (
          match t.t_desc with
            | FunApp(f,tl) when f.f_name = "" ->
                (* decompose if tuple *)
                List.map (fun t -> t.t_type) tl
            | _ -> [ t.t_type ]
        )

let pat_tuple_types pat =
  match !Settings.front_end with
    | Settings.Oracles ->
        (
          match pat with
            | PatTuple (f,pl) when f.f_name = "" ->
                List.map (Terms.get_type_for_pattern) pl
            | _ -> Parsing_helper.internal_error "An oracle argument must be a pattern with a function tuple"
        )
    | Settings.Channels ->
        (
          match pat with
            | PatTuple (f,pl) when f.f_name = "" ->
                (* if we are given a tuple, decompose it *)
                List.map (Terms.get_type_for_pattern) pl
            | _ -> [Terms.get_type_for_pattern pat]
        )

let file_loading opt =
  let read_files acc = function
      Read (b,f) ->
        let ser=get_read_serial b.btype in
          ("\n"^(get_binder_name b)^" = "^(func_call ser ("base.read_file('"^f^"')")))^acc
    | _ -> acc
  in
    List.fold_left read_files "" opt

let write_file opt b =
  match
    (List.filter
       (function
          | Write (b',_) -> b==b'
          | _ -> false
       ) opt)
  with
    | Write(b,f)::_ ->
        let ser = get_write_serial b.btype in
          "\n"^"base.write_file('"^f^"', "^(func_call ser (get_binder_name b))^")"
    | _ -> ""

let random b =
  let rand = match b.btype.trandom with
      Some(r) -> r
    | None -> error ("Random generation function required for type "^b.btype.tname^" required.")
  in
    "\n"^(get_binder_name b)^" = "^rand

let yield_transl _ = "\n"^"raise Exception('Bad argument')"

let processes : string list ref = ref []
let rec translate_oprocess opt (p:process) (inst_vars:BinderSet.t) ind =
  match p.p_desc with
    | Yield -> yield_transl ""
    | EventAbort _ -> "\n"^"raise base.Abort()"
    | Restr(b,p) ->
        (random b)^
        (write_file opt b)^
        (translate_oprocess opt p inst_vars "")
    | Test(t,p1,p2) ->
        "\nif "^(translate_term t inst_vars "")^":\n"^
        indent (translate_oprocess opt p1 inst_vars "")^
        "\nelse:\n"^
        indent (translate_oprocess opt p2 inst_vars "")
    | Output((c,_),t,p) ->
        let proc_name = create_fresh_name "proc_" in
        "\n"^(
        if term_tuple_types t = [] then
          (* Function doesn't take any arguments, there are no free variables *)
          match p.i_desc with
            (* There is no function *)
            | Nil -> "return None"
            | _ ->
                let proc_body = translate_process opt p proc_name in
                let proc = "def "^proc_name^"():\n"^(indent proc_body) in
                processes := proc :: !processes;
                "return "^proc_name
        (* There are free varibles in this function that need to be passed in before
         * it can be called *)
        else
          let output_terms = translate_term_to_output t inst_vars "" in
          match p.i_desc with
            (* No-op process *)
            | Nil -> "return (None, "^output_terms^")\n"
            (* Regular input process *)
            | _ ->
                let (fv,_,_) = iprocess_get_vars p in
                let get_oracle_names = List.map (fun (_,oname,_,_) -> get_oracle_name oname) in
                let ctor_args  = string_list_sep ", " (List.map (fun v -> get_local_var_name v inst_vars)
                                                                (BinderSet.elements fv)) in
                let proc = translate_process opt p proc_name in
                let oracles = get_oracle_names (get_next_oracles true p) in
                let next_oracles = tuple_or_bare ((^) "pnext.") oracles in
                processes := proc :: !processes;
                "pnext = "^(func_call proc_name ctor_args)^"\n"^
                "return ("^next_oracles^", "^output_terms^")")
    | Let(pat,t,p1,p2) ->
        "\n"^match_pattern opt pat (translate_term t inst_vars "") (translate_oprocess opt p1 inst_vars) (translate_oprocess opt p2 inst_vars) false inst_vars ""
    | EventP(t,p)->
        translate_oprocess opt p inst_vars ""
    | Find(_,_,_) ->
        error "Find not supported"
    | Get(tbl,patl,topt,p1,p2) ->
        translate_get opt tbl patl topt (translate_oprocess opt p1 inst_vars) (translate_oprocess opt p2 inst_vars) inst_vars ""
    | Insert(tbl,tl,p) ->
        let tfile = get_table_file tbl in
        let records = List.map2 (fun t ty -> (func_call (get_write_serial ty)
                                                        (translate_term t inst_vars "")))
                                tl tbl.tbltype in
          "\nbase.insert_into_table('"^tfile^"', ["^(string_list_sep ", " records)^"])\n"^
            (translate_oprocess opt p inst_vars "")


(* p1 and p2 are functions that take the indentation level and returns the string corresponding to the program *)
and translate_get opt tbl patl topt p1 p2 inst_vars ind =
  let tfile = get_table_file tbl in
  let input_list = create_fresh_name "list_" in
  let output_list = create_fresh_name "list_" in
  let tvars1 = create_fresh_names "tvar_" (List.length tbl.tbltype) in
  let tvars = create_fresh_names "tvar_" (List.length tbl.tbltype) in
    "\n"^input_list^" = "^(func_call "base.get_from_table" ("'"^tfile^"'"))^"\n"^
    output_list^" = []\n"^
    "for ("^(string_list_sep ", " tvars1)^") in "^input_list^":\n"^
      (indent (
        "("^(string_list_sep ", " tvars)^") = ("^(string_list_sep ", "
                                                    (List.map2 (fun v t -> func_call (get_read_serial t) v)
                                                               tvars1 tbl.tbltype))^")\n"^
        (match_pattern_list
          opt patl tvars
          (fun _ ->
            match topt with
              Some t ->
                "if "^(translate_term t inst_vars "")^":\n"^
                (indent (output_list^".append(("^(string_list_sep ", " tvars)^"))"))
            | None -> (output_list^".append(("^(string_list_sep ", " tvars)^"))"))
          (fun _ -> "pass")
          false
          inst_vars
          "")
        ))^
      "\nif not "^output_list^":\n"^
      (indent (p2 ""))^
      "\nelse:\n"^
      (indent (
        "("^(string_list_sep ", " tvars)^") = base.random_list("^output_list^")\n"^
        (match_pattern_list opt patl tvars p1 yield_transl false inst_vars "")))

and translate_term (t:term) (inst_vars:BinderSet.t) ind =
  let rec termlist sep = function
      [] -> ""
    | [a] -> translate_term a inst_vars ""
    | a::b -> (translate_term a inst_vars "")^sep^(termlist sep b)
  in
    match t.t_desc with
      | Var (b,tl) ->
          let bname = get_binderref_name t.t_loc (b,tl) in
          get_local_var_name bname inst_vars
      | FunApp(f,tl) ->
          if f.f_name = "" then
            "base.compose(["^
            (string_list_sep ", " (List.map
              (fun t -> func_call (get_write_serial t.t_type) (translate_term t inst_vars "")) tl))^
            "])"
          else begin
            match f.f_name with
            | "="  -> termlist " == " tl
            | "<>" -> termlist " != " tl
            | _    -> match f.f_impl with
                      | Func x  -> func_call x (termlist ", " tl)
                      | Const x -> x
                      | No_impl -> error ("Function not registered:" ^ f.f_name)
            end
      | TestE(t1,t2,t3) -> "("^(translate_term t2 inst_vars "")^" if "^(translate_term t1 inst_vars "")^" else "^(translate_term t3 inst_vars "")^")"
      | ReplIndex _ -> Parsing_helper.input_error "Replication indices should occur only inside variables (implementation)" t.t_loc
      | EventAbortE _ -> Parsing_helper.input_error "Events not allowed in terms (implementation)" t.t_loc
      | FindE _ -> Parsing_helper.input_error "Find not supported (implementation)" t.t_loc
      | ResE (b,t) -> func_call (random b) (translate_term t inst_vars "")
      | LetE (pat, t1, t2, topt) ->
          "("^(match_pattern [] pat (translate_term t1 inst_vars "") (translate_term t2 inst_vars)
	    (match topt with
	      Some t3 -> translate_term t3 inst_vars
	    | None -> (fun _ -> Parsing_helper.internal_error "else branch of let called but not defined")) true inst_vars "")^")"

and translate_term_to_output t inst_vars ind =
  match !Settings.front_end with
    | Settings.Oracles ->
        (
          match t.t_desc with
            | FunApp(f,tl) when f.f_name="" ->
                let terms = List.map (fun t -> translate_term t inst_vars "") tl in
                string_list_sep ", " terms
            | _ -> Parsing_helper.internal_error "output term not of the form \"\"()"
        )
    | Settings.Channels ->
        (
          match t.t_desc with
            | FunApp(f,tl) when f.f_name="" ->
                let terms = List.map (fun t -> translate_term t inst_vars "") tl in
                string_list_sep ", " terms
            | _ -> translate_term t inst_vars ""
        )

and match_pattern_complex opt (pat:pattern) (s:string) (p1:string->string) (p2:string->string) (in_term:bool) (inst_vars:BinderSet.t) ind =
  (*decomposition of every function*)
  let rec decompos : pattern -> (string list*string*(string*string) list) = function
    | PatVar(b) ->
        ([],get_binder_name b,[])
    | PatEqual(t) ->
        let n=create_fresh_name "bvar_" in
          ([],n,[(n, translate_term t inst_vars "")])
    | PatTuple(f,pl) ->
        let n=create_fresh_name "bvar_" in
        let func (vl:string list) =
          if f.f_name = "" then
            let l = create_fresh_name "lvar_" in
            let plength = List.length pl in
            let cl = create_fresh_names "cvar_" plength in
            let assignments1 = List.map2 (fun p n ->
                  func_call (get_read_serial (Terms.get_type_for_pattern p)) n) pl cl in
            let assignments2 = List.map2 (fun v a ->
                  v^" = "^a) vl assignments1 in
              l^" = base.decompose("^n^")\n"^
              "if len("^l^") != "^(string_of_int plength)^":\n"^
              (indent "raise base.MatchFail()")^"\n"^
              "("^(string_list_sep ", " cl)^") = "^l^"\n"^
              (string_list_sep "\n" assignments2)
          else
            (
              match (f.f_impl_inv) with
                  (* Simple inverse function application *)
                  Some(f) ->
                    let lhs = (match vl with [x] -> x | _ -> "("^(string_list_sep ", " vl)^")") in
                    let rhs = func_call f n in
                    lhs^" = "^rhs
                | _ -> error ("Inverse function of "^f.f_name^" not registered. Add a line 'implementation fun "^f.f_name^"=\"f1\" [inverse = \"f2\"].' in the source.")
            )
        in
        let decompos_list = List.map decompos pl in
        let vl = List.map (fun (x,y,z)->y) decompos_list in
          (
            (* func *)
            (func vl)::
              (List.concat (List.map (fun (x,y,z)->x) decompos_list)),
            (* name *)
            n,
            (* tests *)
            List.concat (List.map (fun (x,y,z)-> z) decompos_list)
          )
  in
  let rec get_all_binders=function
    | PatVar(b) -> [b]
    | PatTuple(f,pl) -> List.concat (List.map get_all_binders pl)
    | _ -> []
  in
  let all_binders = get_all_binders pat in
  let rec andlist = function
    | [] -> "True"
    | [x] -> x
    | x::y -> x^" and "^(andlist y)
  in
  let (func,name,tests) = decompos pat in
    "try:\n"^
    (indent (
      name^" = "^s^
      (*decompos functions*)
      (List.fold_left (^) ""
         (List.map (fun body -> "\n"^body) func)
      )^
      (*tests*)
      "\n\n"^"if "^(andlist (List.map (fun (n, s)-> n^" == "^s) tests))^":\n"^
      (indent ((if not in_term then
         (string_list_sep_ignore_empty ""
            (List.map (fun s -> write_file opt s)
                      all_binders))
          else "")^
        (p1 "")))^"\n"^
      "else:\n"^indent ("raise base.MatchFail()")))^
    "\nexcept base.MatchFail:\n"^(indent (p2 ""))

and match_pattern opt (pat:Types.pattern) (var:string) (p1:string -> string) (p2: string -> string) (in_term:bool) (inst_vars:BinderSet.t) ind =
  match pat with
    | PatVar(b) ->
        (get_binder_name b)^" = "^var^(if (not in_term) then write_file opt b else "")^"\n"^(p1 "")
    | PatEqual(t) ->
        "if "^var^" == "^(translate_term t inst_vars "")^":\n"^
        indent (p1 "")^
        "\n"^"else:\n"^
        indent (p2 "")
    | _ -> match_pattern_complex opt pat var p1 p2 in_term inst_vars ""

and match_pattern_list opt patl vars (p1:string -> string) (p2:string -> string) in_term inst_vars ind =
  (List.fold_right2 (fun pat var acc _ -> match_pattern opt pat var acc p2 in_term inst_vars ""^"\n") patl vars p1) ""

and match_pattern_from_input opt pat (vars:string list) (next:string -> string) (inst_vars:BinderSet.t) ind =
  match !Settings.front_end with
    | Settings.Oracles ->
        (
          match pat with
            | PatTuple (f,pl) when f.f_name = "" ->
                match_pattern_list opt pl vars next yield_transl false inst_vars ""
            | _ -> Parsing_helper.internal_error "oracle must begin with pattern \"\"(...)"
        )
    | Settings.Channels ->
        (
          match pat with
            | PatTuple (f,pl) when f.f_name = "" ->
                match_pattern_list opt pl vars next yield_transl false inst_vars ""
            | _ ->
                match vars with
                    [var] ->
                      match_pattern opt pat var next yield_transl false inst_vars ""
                  | _ -> Parsing_helper.internal_error "var in match_pattern_from_input"
        )

and get_oracle_body (opt:impl_opt list) ((token,name,pat,p):string option*string*pattern*process) (inst_vars:BinderSet.t) =
  let args = create_fresh_names "input_" (List.length (pat_tuple_types pat)) in
  let type_list = pat_tuple_types pat in
  let typecheck_list = List.map2 (fun t a ->
                                  let p = get_type_predicate t in
                                    if p = "base.true_pred" then
                                      ""
                                    else
                                      (p^"("^a^")")) type_list args in
  let filter_typecheck_list=List.filter (fun s -> s <> "") typecheck_list in
  let check_list = filter_typecheck_list in
    "\ndef "^(get_oracle_name name)^"("^(string_list_sep ", " ("self"::args))^"):\n"^
    (indent (
      (match token with
        | Some t ->
            "if not self."^t^":\n"^
              indent ("raise base.BadCall()")^
            "\nself."^t^" = False\n\n"
        | _ -> "")^
      if check_list <> [] then
        "if "^(string_list_sep " and " check_list)^":\n"^
        (indent (
          (match_pattern_from_input opt pat args (translate_oprocess opt p inst_vars) inst_vars "")))^
        "\nelse:\n"^
        (indent (
          "raise base.BadCall()"))
      else
        match_pattern_from_input opt pat args (translate_oprocess opt p inst_vars) inst_vars ""))

and set_instance_vars (vars:BinderSet.t) (tokens:string list) : string =
  if BinderSet.is_empty vars && tokens = []
    then "pass"
    else
      (BinderSet.fold (fun v acc ->
        acc^"self."^v^" = "^v^"\n") vars "")^
      (if tokens <> [] then
          (List.fold_right (fun t acc ->
            acc^"self."^t^" = True\n") tokens "")
        else
          "")

and translate_process opt (p:inputprocess) name =
  let ol = get_next_oracles true p in
    match ol with
    | [] -> ""
    | _ ->
        (* Find run-once tokens used in this process *)
        let get_token xs (b, _, _, _) = (match b with
          | Some t -> t::xs
          | _      -> xs) in
        let tokens = List.fold_left get_token [] ol in
        (* Set of free varibles passed from parent process *)
        let (fv, _, _) = iprocess_get_vars p in
        let ctor_args = (if BinderSet.is_empty fv
                          then ""
                          else ", "^(string_list_sep ", " (BinderSet.elements fv))) in
        "class "^name^":\n"^
        indent (
          "def __init__(self"^ctor_args^"):\n"^
          indent (
            (set_instance_vars fv tokens)^"\n")^
          (string_list_sep "\n"
            (List.map (fun o -> get_oracle_body opt o fv) ol)))

let impl_init (opt:impl_opt list) (p:inputprocess) =
  processes := [];
  let (fv, _, _) = iprocess_get_vars p in
  let proc_top   = translate_process opt p "proc_top" in
  let all_procs  = string_list_sep "\n\n" (proc_top :: !processes) in
  "def init():\n"^
  (indent (
    (file_loading opt)^"\n"^(
    let get_oracle_names = List.map (fun (_, oname, _, _) -> get_oracle_name oname) in
    let oracles = get_oracle_names (get_next_oracles true p) in
    let next_oracles = tuple_or_bare ((^) "p.") oracles in
    "p = proc_top("^(string_list_sep ", " (BinderSet.elements fv))^")\n"^
    "return "^next_oracles)))^"\n\n"^
  all_procs

let get_implementation (opt:impl_opt list) (p:inputprocess) =
  "import base, crypto\n\n"^(impl_init opt p)^"\n"

let impl_translate (process:inputprocess) (opt:impl_opt list) =
  get_implementation opt process

let do_implementation (impl:impl_process list) =
  let dir_sep = "/" (* Filename.dir_sep exists only in OCaml >= 3.11.2 and
		     OCaml MinGW exists only in OCaml 3.11.0... *) in
  let impl = impl_check impl in
  List.iter
    (fun (x,opt,p)->
        print_string ("Generating implementation for module "^x^"...\n");
        let impl = impl_translate p opt in
        let f = open_out ((!Settings.out_dir)^dir_sep^x^".py") in
          output_string f impl;
          close_out f;
          print_string ("Done.\n")
    ) impl

(* vim: set et ts=8 sw=2 tw=0: *)
