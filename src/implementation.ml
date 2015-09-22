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


module StringMap = Map.Make(String)
module BinderSet = Set.Make(String)


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

(*informations to the user*)
let info mess = print_string ("Information: "^ mess^" (implementation)\n")
let error mess = Parsing_helper.user_error ("Error: "^mess^" (implementation)\n")

let string_list_sep = String.concat

let string_list_sep_ignore_empty sep t=
  string_list_sep sep (List.filter (fun s -> s <> "") t)

let is_alphabetic c=
  (c>='A' && c <='Z') || (c>='a' && c <='z') || (c>='0' && c <='9')

let hex_of_char c=
  Printf.sprintf "%02x" (int_of_char c)

let alphabetize_string s=
  let buf = ref "" in
  String.iter (fun c ->
    buf := (!buf)^
       (if is_alphabetic c then
	 String.make 1 c
       else
         "_"^(hex_of_char c))
    ) s;
  !buf

let get_oracle_name name =
  "oracle_"^(alphabetize_string name)

let get_binder_name b =
  "var_"^(alphabetize_string b.sname)^"_"^(string_of_int b.vname)

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

let empty_bv = BinderSet.empty
let bound_bv = BinderSet.singleton
let add_bv = BinderSet.union

let add_list_bv f l=
  List.fold_left (fun x y -> add_bv x (f y)) empty_bv l

let get_binderref_name ext (b,l) =
  if Terms.is_args_at_creation b l then
    get_binder_name b
  else
    Parsing_helper.input_error "There should not be any find variable (implementation)" ext

let get_local_var_name bname iv =
  if BinderSet.mem bname iv then
    "self."^bname
  else
    bname

let free_vars = ref BinderSet.empty (* Contains all free variables; may contain some variables that are also bound *)
let bound_vars_under_repl = ref BinderSet.empty

let free_var b =
  free_vars := BinderSet.add b (!free_vars);
  BinderSet.empty

let rec get_pattern_bv = function
    PatVar(b)->bound_bv (get_binder_name b)
  | PatTuple((fs,pl))-> add_list_bv get_pattern_bv pl
  | PatEqual(t)->get_term_bv t
and get_iprocess_bv p =
  match p.i_desc with
      Nil -> empty_bv
    | Input((c,tl),pat,p) ->
        add_bv (get_oprocess_bv p) (get_pattern_bv pat)
    | Par (p1,p2) ->
        add_bv (get_iprocess_bv p1) (get_iprocess_bv p2)
    | Repl(b,p1) ->
	let bv = get_iprocess_bv p1 in
	bound_vars_under_repl := BinderSet.union (!bound_vars_under_repl) bv;
	empty_bv

and get_term_bv t = match t.t_desc with
    Var(b,tl) ->
      free_var (get_binderref_name t.t_loc (b,tl))
  | FunApp(fs,tl) -> add_list_bv get_term_bv tl
  | TestE(t1,t2,t3) ->
      add_bv
        (add_bv (get_term_bv t1) (get_term_bv t2))
        (get_term_bv t3)
  | LetE(pat,t1,t2,t3) ->
      add_bv (get_pattern_bv pat)
	(add_bv (get_term_bv t1)
	   (add_bv (get_term_bv t2)
	      (match t3 with
		None -> empty_bv
              | Some(t) -> get_term_bv t)))
  | ResE(b,t) ->
      add_bv (bound_bv (get_binder_name b))
        (get_term_bv t)
  | ReplIndex _ -> Parsing_helper.input_error "Replication indices should occur only inside variables (implementation)" t.t_loc
  | EventAbortE _ -> Parsing_helper.input_error "Events not allowed in terms (implementation)" t.t_loc
  | FindE _ -> Parsing_helper.input_error "Find not supported (implementation)" t.t_loc

and get_oprocess_bv p =
  match p.p_desc with
      Yield | EventAbort _ -> empty_bv
    | Restr(b,p) ->
        add_bv
          (bound_bv (get_binder_name b))
          (get_oprocess_bv p)
    | Test(t,p1,p2) ->
        add_bv
          (get_term_bv t)
          (add_bv
             (get_oprocess_bv p1)
             (get_oprocess_bv p2))
    | Output((c,tl),t,p) ->
        add_bv (get_term_bv t) (get_iprocess_bv p)
    | Let(pat,t,p1,p2) ->
        add_bv
          (add_bv (get_pattern_bv pat) (get_term_bv t))
          (add_bv (get_oprocess_bv p1) (get_oprocess_bv p2))
    | EventP(t,p)->
        get_oprocess_bv p
    | Find(fl,ep,_) ->
        error "Find not supported"
    | Get(tbl,patl,topt,p1,p2) ->
        (List.fold_right add_bv (List.map get_pattern_bv patl)
           (add_bv
              (match topt with Some t -> get_term_bv t | None -> empty_bv)
              (add_bv (get_oprocess_bv p1) (get_oprocess_bv p2))))
    | Insert(tbl,tl,p) ->
        List.fold_right add_bv (List.map get_term_bv tl)
          (get_oprocess_bv p)

let iprocess_get_vars (p:inputprocess) =
  free_vars := BinderSet.empty;
  bound_vars_under_repl := BinderSet.empty;
  let bv_no_repl = get_iprocess_bv p in
  let fv = BinderSet.diff (!free_vars) (BinderSet.union bv_no_repl (!bound_vars_under_repl)) in
  let bv_repl = (!bound_vars_under_repl) in
  free_vars := BinderSet.empty;
  bound_vars_under_repl := BinderSet.empty;
  (fv, bv_no_repl, bv_repl)

let oprocess_get_vars (p:process) =
  free_vars := BinderSet.empty;
  bound_vars_under_repl := BinderSet.empty;
  let bv_no_repl = get_oprocess_bv p in
  let fv = BinderSet.diff (!free_vars) (BinderSet.union bv_no_repl (!bound_vars_under_repl)) in
  let bv_repl = (!bound_vars_under_repl) in
  free_vars := BinderSet.empty;
  bound_vars_under_repl := BinderSet.empty;
  (fv, bv_no_repl, bv_repl)

(* Check if the free variables of roles are all written to files. *)
let impl_check impllist =
  let bf=StringMap.empty in
  let boundfiles = ref bf in

  let check_read (pn,p,vars,opt) =
    let rec read_opt1 (fv,bv_no_repl,bv_repl) = function
        Read(b,f)::next ->
	  let bname = get_binder_name b in
          if BinderSet.mem bname fv then
            read_opt1 (BinderSet.remove bname fv,bv_no_repl,bv_repl) next
          else
            error ("Module "^pn^" reads variable "^bname^", which is not free.")
      | _::next ->
          read_opt1 (fv,bv_no_repl,bv_repl) next
      | [] -> (fv,bv_no_repl,bv_repl)
    in
    (pn,p,read_opt1 vars opt,opt)
  in
  let check_write (pn,p,vars,opt) =
    let rec read_opt2 (fv,bv_no_repl,bv_repl) = function
      | Write(b,f)::next ->
	  let bname = get_binder_name b in
          if BinderSet.mem bname bv_no_repl then
            (
              boundfiles := StringMap.add bname (b,f) (!boundfiles);
              read_opt2 (fv,BinderSet.remove bname bv_no_repl,bv_repl) next
            )
          else if BinderSet.mem bname bv_repl then
	    error ("Module "^pn^" writes variable "^bname^", which is bound under a replication in that module.")
	  else
            error ("Module "^pn^" writes variable "^bname^", which is not bound.")
      | _::next ->
          read_opt2 (fv,bv_no_repl,bv_repl) next
      | [] -> (fv,bv_no_repl,bv_repl)
    in
    (pn,p,read_opt2 vars opt,opt)
  in
  let add_files (pn,p,(fv,_,_),opt) =
    let opt = BinderSet.fold
      (fun s opt ->
         (*is it a variable written by a previous process ? *)
         try
	   let (b,f) =  StringMap.find s (!boundfiles) in
           info (pn^" will read "^(s)^" from file "^f^".");
           (Read(b,f))::opt
         with Not_found ->
           error ("Module "^pn^" needs to read the variable "^(s)^", but no module writes it.")
      ) fv opt
    in
    (pn,opt,p)
  in
  (*get variables *)
  let vars = List.map (fun ((pn,opt,p):impl_process) -> (pn,p,iprocess_get_vars p,opt)) impllist in
  List.map add_files
    (List.map check_read (List.map check_write vars))

let rt = ref 0

let create_fresh_number () =
  rt := !rt + 1;
  !rt

let create_fresh_name prefix =
  prefix^(string_of_int (create_fresh_number ()))

let rec create_fresh_names prefix = function
    0 -> []
  | i -> (create_fresh_name prefix)::(create_fresh_names prefix (i-1))

let check_oracle_compatibility name (rt, o) (rt', o') =
  if (rt <> rt') then
    match !Settings.front_end with
      | Settings.Channels ->
          error ("The outputs following inputs on channel "^name^
                    " do not have the same type")
      | Settings.Oracles ->
          error ("The oracle "^name^
                    " does not have the same return types everywhere")
  else if (o <> o') then
    match !Settings.front_end with
      | Settings.Channels ->
          error ("The input channels after outputs after inputs on channel "^name^
                    " are not the same everywhere")
      | Settings.Oracles ->
          error ("The oracle "^name^
                    " does not have the same next oracles everywhere")

let check_argument_type_compatibility name at at' =
  if (at <> at') then
    match !Settings.front_end with
      | Settings.Channels ->
          error ("The messages of inputs on channel "^name^
                    " do not have the same types everywhere")
      | Settings.Oracles ->
          error ("The arguments of oracle "^name^
                    " do not have the same types everywhere")

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

let get_type_predicate t =
  match t.tpredicate with
    | Some x -> x
    | None -> error ("Predicate for type "^t.tname^" required!")

let get_table_file tbl =
  match tbl.tblfile with
    | None -> error ("No file given for the table "^tbl.tblname)
    | Some f -> f

let get_read_serial ty =
  match ty.tserial with
    | Some (_,s) -> s
    | None -> error ("Serialization for type "^ty.tname^" required")

let get_write_serial ty =
  match ty.tserial with
    | Some (s,_) -> s
    | None -> error ("Serialization for type "^ty.tname^" required")

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

(* BEGIN AUX *)
and string_of_iprocess p = string_of_iprocess_desc p.i_desc
and string_of_iprocess_desc = function
  | Nil -> "nil"
  | Par (p1, p2) -> "(par "^(string_of_iprocess p1)^" "^(string_of_iprocess p2)^")"
  | Repl (ri, p) -> "(repl "^(string_of_repl_index ri)^" "^(string_of_iprocess p)^")"
  | Input ((c, l), pat, p) ->
      let tlist = string_of_list (List.map string_of_term l) in
      "(input '"^(c.cname)^" "^tlist^" "^(string_of_pattern pat)^" "^
        (string_of_process p)^")"

and string_of_process p = string_of_process_desc p.p_desc
and string_of_process_desc = function
  | Yield -> "(yield)"
  | EventAbort f -> "(event-abort "^(string_of_fdesc f)^")"
  | Restr (b, p) -> "(random "^(string_of_binder b)^" "^(string_of_process p)^")"
  | Test (t, p1, p2) -> "(test "^(string_of_term t)^" "^(string_of_process p1)^" "^(string_of_process p2)^")"
  | Find (_, p, _) -> "(find 'list "^(string_of_process p)^" 'find-info)"
  | Output ((c, l), t, ip) ->
      let tlist = string_of_list (List.map string_of_term l) in
      "(output '"^(c.cname)^" "^tlist^" "^(string_of_term t)^" "^
        (string_of_iprocess ip)^")"
  | Let (pat, t, p1, p2) -> "(let "^(string_of_pattern pat)^" "^(string_of_term t)^" "^
      (string_of_process p1)^" "^(string_of_process p2)^")"
  | EventP (t, p) -> "(event "^(string_of_term t)^" "^(string_of_process p)^")"
  | Insert (_, tl, p) -> "(insert 'table "^(string_of_list (List.map string_of_term tl))^" "^
      (string_of_process p)^")"
  | Get (_, patl, t, p1, p2) -> "(insert 'table "^(string_of_list (List.map string_of_pattern patl))^
      " "^(match t with Some x -> string_of_term x | _ -> "nil")^" "^(string_of_process p1)^" "^
      (string_of_process p2)^")"
and string_of_pattern = function
  | PatVar b -> "(pat-var "^(string_of_binder b)^")"
  | PatTuple (f, patl) -> "(pat-tuple "^(string_of_fdesc f)^" "^(string_of_list (List.map
      string_of_pattern patl))^")"
  | PatEqual t -> "(pat-eq "^(string_of_term t)^")"
and string_of_term t = string_of_term_desc t.t_desc
and string_of_term_desc = function
  | Var (b, tl) ->
      let terms = List.map string_of_term tl in
      if terms = [] then
        string_of_binder b
      else
        "(at "^(string_of_binder b)^" "^(string_of_list terms)^")"
  | ReplIndex ri -> "(repl-index "^(string_of_repl_index ri)^")"
  | FunApp (f, tl) ->
      let terms = string_of_list (List.map string_of_term tl) in
      if f.f_name = "" then
        terms
      else
        "(app "^(string_of_fdesc f)^" "^terms^")"
  | TestE _ -> "'test-e"
  | FindE _ -> "'find-e"
  | LetE (pat, t1, t2, t3) -> "(let "^(string_of_pattern pat)^" "^(string_of_term t1)^" "^
      (string_of_term t2)^" "^(match t3 with
        | Some x -> string_of_term x
        | _      -> "nil")^")"
  | ResE (b, t) -> "(res "^(string_of_binder b)^" "^(string_of_term t)^")"
  | EventAbortE _ -> "'event-abort"
and string_of_fdesc fd =
  if fd.f_name = "" then
    "nil"
  else
    "'"^(fd.f_name)
and string_of_binder b =
  "'"^b.sname^"_"^(string_of_int b.vname)
and string_of_repl_index i =
  "'"^i.ri_sname^"_"^(string_of_int i.ri_vname)
and string_of_list = function
  | [] -> "'()"
  | xs -> "(list "^(String.concat " " xs)^")"

and string_of_vars (fv,bv_no_repl,bv_repl) =
  let string_set_sep sep set = string_list_sep sep (BinderSet.elements set) in
  "FV={"^(string_set_sep " " fv)^"} BVN={"^(string_set_sep " " bv_no_repl)^"} BVR={"^
  (string_set_sep " " bv_repl)^"}"
(* END AUX *)

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

let prefix =
  ref "import base, crypto\n\n"

let get_implementation (opt:impl_opt list) (p:inputprocess) =
  (*"'''\n"^(string_of_iprocess p)^"\n'''\n\n"^*)
  (!prefix)^(impl_init opt p)^"\n"

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
