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


module StringMap = Map.Make(String)
module BinderSet = Set.Make(String)


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
  "type_oracle_"^(alphabetize_string name)

let get_binder_name b =
  "var_"^(alphabetize_string b.sname)^"_"^(string_of_int b.vname)


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

let free_vars = ref BinderSet.empty (* Contains all free variables; may contain some variables that are also bound *)
let bound_vars_under_repl = ref BinderSet.empty

let free_var b=
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
		None->empty_bv
              | Some(t)-> get_term_bv t)))
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

let display_vars (a,b)=
  print_string "Free vars : ";
  BinderSet.iter 
    (fun x -> 
       print_string (x^" "))
    a;
  print_newline ();
  print_string "Bound vars : ";
  BinderSet.iter 
    (fun x -> 
       print_string (x^" "))
    b;
  print_newline ()

        
let impl_get_vars p=
  free_vars := BinderSet.empty;
  bound_vars_under_repl := BinderSet.empty;
  let bv_no_repl = get_iprocess_bv p in
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
  let vars = List.map (fun ((pn,opt,p):impl_process) -> (pn,p,impl_get_vars p,opt)) impllist in
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

let type_append = 
  StringMap.fold 
    (fun name (s,at) acc -> 
       try
         (
           let (s',at') = StringMap.find name acc in
           check_argument_type_compatibility name at at';
           match s,s' with
             | Some (rt,o), Some (rt',o') ->
                 check_oracle_compatibility name (rt, o) (rt', o');
                 acc
             | None, Some(rt,o) ->
                 acc
             | Some(rt,o), None ->
                 StringMap.add name (Some(rt,o),at) (StringMap.remove name acc)
             | None, None ->
                 acc
         )
       with Not_found -> 
         StringMap.add name (s,at) acc)

(* returns the next oracles. b represents if the oracle is under replication (false) or not (true) *)

let rec get_next_oracles b p =
  match p.i_desc with
    | Nil -> []
    | Input((c,tl),pat,p) -> 
        [(b,c.cname,pat,p)]
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
        

let rec get_oracle_types_oprocess name args_types p = 
  match p.p_desc with
    | Yield | EventAbort _ -> StringMap.add name (None, args_types) StringMap.empty
    | Restr(b,p) -> 
        get_oracle_types_oprocess name args_types p
    | Test(t,p1,p2) ->
        type_append (get_oracle_types_oprocess name args_types p1) (get_oracle_types_oprocess name args_types p2)
    | Output((c,tl),t,p) -> 
        let r = get_oracle_types_process p in
        let o = List.map (fun (b,n,_,_) -> (b,n)) (get_next_oracles true p) in
        let ra = term_tuple_types t
        in
          (
            try 
              let (s,a') = StringMap.find name r in
              check_argument_type_compatibility name a' args_types;
              match s with 
                | Some (ra',o') -> 
                    check_oracle_compatibility name (ra, o) (ra', o');
                    r        
                | None ->
                    type_append (StringMap.add name (Some(ra,o),args_types) StringMap.empty) r
            with
              | Not_found -> 
                  StringMap.add name (Some(ra,o),args_types) r
          )
    | Let(pat,t,p1,p2) ->
        type_append (get_oracle_types_oprocess name args_types p1) (get_oracle_types_oprocess name args_types p2)
    | EventP(t,p)->
        get_oracle_types_oprocess name args_types p
    | Find(_,_,_) -> 
        error "Find not supported"
    | Get(tbl,patl,topt,p1,p2) ->
        type_append (get_oracle_types_oprocess name args_types p1) (get_oracle_types_oprocess name args_types p2)
    | Insert(tbl,tl,p) ->
        get_oracle_types_oprocess name args_types p
          
          
and get_oracle_types_process p =
  match p.i_desc with
    | Nil -> StringMap.empty
    | Input((c,tl),pat,p) -> 
        get_oracle_types_oprocess c.cname (pat_tuple_types pat) p
    | Par (p1,p2) ->
        type_append (get_oracle_types_process p1) (get_oracle_types_process p2)
    | Repl(b,p) -> 
        get_oracle_types_process p

let get_type_name t =
  match t.timplname with
      Some s -> s
    | None -> error ("Type name required for type "^t.tname)

let get_oracles_type_string o =
  if o <> [] then
    "("^(string_list_sep " * " (List.map (fun (_,n) -> get_oracle_name n) o))^")" 
  else
    "unit"
  

let get_type_oracle name (s,args_types) =
  let (ret_types,o) = match s with
    | Some (rt,o) -> rt,o
    | None -> [],[]
  in
  let ol= get_oracles_type_string o in
    (get_oracle_name name)^
      " = "^
      (
        if args_types = [] then 
          "unit" 
        else
          "("^(string_list_sep " * " (List.map get_type_name args_types))^")"
      )^
      " -> "^
      (
        if ret_types = [] then
          ol
        else
          "("^ol^" * "^
            (string_list_sep " * " (List.map get_type_name ret_types))^
            ")"
      )

let get_oracles_types process = 
  "type "^
    string_list_sep "\n and " 
    (StringMap.fold 
       (fun name (s,at) acc -> 
          (get_type_oracle name (s,at))::acc)
       (get_oracle_types_process process) [])
  

let prefix=
  ref ("open Base\n"^
       "open Crypto\n\n")

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

let file_loading opt ind =
  let read_files acc = function
      Read (b,f) -> 
        let ser=get_read_serial b.btype in
          ("\n"^ind^"let "^(get_binder_name b)^"= exc_bad_file \""^f^"\" "^ser^" (input_string_from_file \""^f^"\") in")^acc
    | _ -> acc
  in
    List.fold_left read_files "" opt

let write_file opt b ind =
  match 
    (List.filter 
       (function
          | Write (b',_) -> b==b'
          | _ -> false
       ) opt) 
  with
    | Write(b,f)::_ -> 
        let ser=get_write_serial b.btype in
          "\n"^ind^"output_string_to_file \""^f^"\" ("^ser^" "^(get_binder_name b)^");"
    | _ -> ""

let random b ind =
  let rand = match b.btype.trandom with
      Some(r) -> r
    | None -> error ("Random generation function required for type "^b.btype.tname^" required.")
  in
    "\n"^ind^"let "^(get_binder_name b)^" = "^rand^" () in"

let yield_transl ind = "\n"^ind^"raise Match_fail"

let rec translate_oprocess opt p ind =
  match p.p_desc with
    | Yield -> yield_transl ind
    | EventAbort _ -> "\n"^ind^"raise Abort"
    | Restr(b,p) -> 
        (random b ind)^
        (write_file opt b ind)^
        (translate_oprocess opt p ind)
    | Test(t,p1,p2) ->
        "\n"^ind^"if "^(translate_term t ind)^" then\n"^ind^"begin"^
          (translate_oprocess opt p1 (ind^"  "))^
          "\n"^ind^"end\n"^ind^"else\n"^ind^"begin"^
          (translate_oprocess opt p2 (ind^"  "))^"\n"^ind^"end"
    | Output((c,tl),t,p) -> 
        if term_tuple_types t = [] then
          (translate_process opt p ind)
        else
          "\n"^ind^"("^(translate_process opt p (ind^"  "))^
            "\n"^ind^"  ,"^(translate_term_to_output t ind)^
            "\n"^ind^")"
    | Let(pat,t,p1,p2) ->
        "\n"^ind^match_pattern opt pat (translate_term t ind) (translate_oprocess opt p1) (translate_oprocess opt p2) false ind
    | EventP(t,p)->
        translate_oprocess opt p ind
    | Find(_,_,_) -> 
        error "Find not supported"
    | Get(tbl,patl,topt,p1,p2) ->
        translate_get opt tbl patl topt (translate_oprocess opt p1) (translate_oprocess opt p2) ind
    | Insert(tbl,tl,p) ->
        let tfile=get_table_file tbl in
          "\n"^ind^"insert_in_table \""^tfile^"\" ["^(string_list_sep "; " (List.map2 (fun t ty -> "("^(get_write_serial ty)^" ("^(translate_term t ind)^"))") tl tbl.tbltype))^"];\n"^
            (translate_oprocess opt p ind)


(* p1 and p2 are functions that take the indentation level and returns the string corresponding to the program *)
and translate_get opt tbl patl topt p1 p2 ind =
  let tfile = get_table_file tbl in
  let list=create_fresh_name "list_" in
  let tvars1 = create_fresh_names "tvar_" (List.length tbl.tbltype) in
  let tvars = create_fresh_names "tvar_" (List.length tbl.tbltype) in
    "\n"^ind^"let "^list^" = get_from_table \""^tfile^"\"\n"^ind^
      "  (function\n"^ind^
      "      | ["^(string_list_sep "; " tvars1)^"] -> begin\n"^ind^
      "        let ("^(string_list_sep "," tvars)^")=("^(string_list_sep "," (List.map2 (fun v t -> "(exc_bad_file \""^tfile^"\" "^(get_read_serial t)^" "^v^")") tvars1 tbl.tbltype))^") in"^
      (
        match_pattern_list 
          opt patl tvars 
          (fun ind ->
             match topt with 
               Some t -> "\n"^ind^"if ("^(translate_term t ind)^") then ("^
		 (string_list_sep "," tvars)^") else raise Match_fail"
             | None -> "("^(string_list_sep "," tvars)^")")
          (fun ind -> "raise Match_fail")
          false
          (ind^"        ")
      )^"\n"^ind^
      "        end\n"^ind^
      "      | _ -> raise (Bad_file \""^tfile^"\")) in\n"^ind^
      "if "^list^" = [] then begin"^
      (p2 (ind^"  "))^
      "\n"^ind^"end else begin\n"^ind^
      "  let ("^(string_list_sep "," tvars)^") = rand_list "^list^" in"^
      (match_pattern_list opt patl tvars p1 yield_transl false (ind^"  "))^"\n"^ind^"end"
      
and translate_term t ind =
  let rec termlist sep = function
      [] -> "()"
    | [a] -> translate_term a ind
    | a::b -> (translate_term a ind)^sep^(termlist sep b)
  in
    match t.t_desc with
      | Var (b,tl) -> get_binderref_name t.t_loc (b,tl)
      | FunApp(f,tl) -> 
          if f.f_name = "" then
            "(compos ["^
            (string_list_sep ";" (List.map (fun t -> (get_write_serial t.t_type)^" "^(translate_term t ind)) tl))^
            "])"
          else
            (match f.f_impl with 
                 Func x -> "("^x^" "^(termlist " " tl)^")"
               | Const x -> x
               | No_impl -> error ("Function not registered:" ^ f.f_name)
            )
      | TestE(t1,t2,t3) -> "(if "^(translate_term t1 ind)^" then "^(translate_term t2 ind)^" else "^(translate_term t3 ind)^" )"
      | ReplIndex _ -> Parsing_helper.input_error "Replication indices should occur only inside variables (implementation)" t.t_loc
      | EventAbortE _ -> Parsing_helper.input_error "Events not allowed in terms (implementation)" t.t_loc
      | FindE _ -> Parsing_helper.input_error "Find not supported (implementation)" t.t_loc
      | ResE (b,t) -> "("^(random b ind)^" "^(translate_term t ind)^")"
      | LetE (pat, t1, t2, topt) -> 
          "("^(match_pattern [] pat (translate_term t1 ind) (translate_term t2) 
	    (match topt with 
	      Some t3-> translate_term t3 
	    | None -> (fun ind -> Parsing_helper.internal_error "else branch of let called but not defined")) true ind)^")"

and translate_term_to_output t ind =
  match !Settings.front_end with
    | Settings.Oracles ->
        (
          match t.t_desc with
            | FunApp(f,tl) when f.f_name="" ->
                string_list_sep ", " (List.map (fun t -> translate_term t ind) tl)
            | _ -> Parsing_helper.internal_error "output term not of the form \"\"()"
        )
    | Settings.Channels ->
        (
          match t.t_desc with
            | FunApp(f,tl) when f.f_name="" ->
                string_list_sep ", " (List.map (fun t -> translate_term t ind) tl)
            | _ -> translate_term t ind
        )
        
and match_pattern_complex opt pat s p1 p2 in_term ind =
  (*decomposition of every function*)
  let rec decompos=function
    | PatVar(b) -> 
        ([],get_binder_name b,[])
    | PatEqual(t) -> 
        let n=create_fresh_name "bvar_" in
          ([],n,[(n, translate_term t ind)])
    | PatTuple(f,pl) -> 
        let n=create_fresh_name "bvar_" in
        let func=
          if f.f_name = "" then
            let n = create_fresh_name "cvar_" in
            let l = create_fresh_name "lvar_" in
            let nl= create_fresh_names "cvar_" (List.length pl) in
              "(fun "^n^" -> let "^l^" = decompos "^n^" in match "^l^" with\n"^
                ind^"    | ["^(string_list_sep ";" nl)^"] -> ("^
                (string_list_sep "," (List.map2 (fun p n -> 
		  (get_read_serial (Terms.get_type_for_pattern p))^" "^n) pl nl))^")\n"^
                ind^"    | _ -> raise Match_fail)"
          else
            (
              match (f.f_impl_inv) with 
                  Some(f) -> f 
                | _ -> error ("Inverse function of "^f.f_name^" not registered. Add a line 'implementation fun "^f.f_name^"=\"f1\" [inverse = \"f2\"].' in the source.")
            )
        in
        let decompos_list = List.map decompos pl in
          (
            (n,func,List.map (fun (x,y,z)->y) decompos_list)::
              (List.concat (List.map (fun (x,y,z)->x) decompos_list)),
            n,
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
    | [] -> "true"
    | [x] -> x
    | x::y -> x^" && "^(andlist y)
  in
  let (func,name,tests) = decompos pat in
    "try\n"^ind^"  let "^name^"="^s^" in"^
      (*decompos functions*)
      (List.fold_left (^) "" 
         (List.map 
            (fun (n,f,vl) -> 
               "\n"^ind^"  let ("^(string_list_sep "," vl)^")="^
                 f^" "^n^" in") func)
      )^
          (*tests*)
      "\n"^ind^"  if "^(andlist (List.map (fun (n,s)-> n^"="^s) tests))^
      " then begin"^
      (if not in_term then
         (string_list_sep_ignore_empty "" 
            (
              (List.map (fun s -> 
                           write_file opt s (ind^"     ")) 
                 all_binders)
            ))
       else "")^
      (p1 (ind^"    "))^
      "\n"^ind^"  end\n"^ind^"  else\n"^ind^"    raise Match_fail\n"^ind^"with Match_fail -> "^(p2 (ind^"  "))

and match_pattern opt (pat:Types.pattern) (var:string) (p1:string -> string) (p2: string -> string) (in_term:bool) ind =
  match pat with
    | PatVar(b) -> 
        "let "^(get_binder_name b)^" = "^var^" in "^(if (not in_term) then write_file opt b (ind^"  ") else "")^(p1 ind)
    | PatEqual(t) -> 
        "if "^(translate_term t ind)^" = "^var^" then\n"^ind^"begin"^
          (p1 (ind^"  "))^
          "\n"^ind^"end else begin "^
          (p2 (ind^"  "))^
          "\n"^ind^"end"
    | _ -> match_pattern_complex opt pat var p1 p2 in_term ind

and match_pattern_list opt patl vars (p1:string -> string) (p2:string -> string) in_term ind =
  (List.fold_right2 (fun pat var acc ind -> "\n"^ind^match_pattern opt pat var acc p2 in_term ind) patl vars p1) ind

and match_pattern_from_input opt pat (vars:string list) (next:string -> string) ind =
  match !Settings.front_end with
    | Settings.Oracles ->
        (
          match pat with
            | PatTuple (f,pl) when f.f_name = "" ->
                match_pattern_list opt pl vars next yield_transl false ind
            | _ -> Parsing_helper.internal_error "oracle must begin with pattern \"\"(...)"
        )
    | Settings.Channels ->
        (
          match pat with
            | PatTuple (f,pl) when f.f_name = "" ->
                match_pattern_list opt pl vars next yield_transl false ind
            | _ -> 
                match vars with
                    [var] ->
                      match_pattern opt pat var next yield_transl false ind
                  | _ -> Parsing_helper.internal_error "var in match_pattern_from_input"
        )


and get_oracle_body opt (b,name,pat,p) ind =
  let args=create_fresh_names "input_" (List.length (pat_tuple_types pat)) in
  let token=create_fresh_name "token_" in
  let type_list=pat_tuple_types pat in
  let typecheck_list=List.map2 (fun t a ->
                                  let p = get_type_predicate t in
                                    if p = "always_true" then
                                      ""
                                    else
                                      ("("^p^" "^a^")")) type_list args in
  let filter_typecheck_list=List.filter (fun s -> s <> "") typecheck_list in
  let check_list=if b then ("(!"^token^")")::filter_typecheck_list else filter_typecheck_list in
    "\n"^ind^"begin\n"^ind^"  "^(
        if b then 
          "let "^token^" = ref true in\n"^ind^"  "
        else ""
      )^
      "fun ("^(string_list_sep ", " args)^") ->\n"^ind^"    "^
      (if check_list <> [] then 
         "if "^(string_list_sep " && " check_list)^" then\n"^ind^"    "^
           "begin\n"^ind^"      "^
           (if b then token^" := false;" else "")^
           match_pattern_from_input opt pat args (translate_oprocess opt p) (ind^"      ")^
           "\n"^ind^"    "^"end\n"^ind^"    "^
           "else raise Bad_call"
       else
         match_pattern_from_input opt pat args (translate_oprocess opt p) (ind^"    ")
      )^"\n"^ind^"end"

and translate_process opt p ind =
  let l = get_next_oracles true p in
    "\n"^ind^"("^
      string_list_sep ("\n"^ind^",") (List.map (fun x -> x (ind^" ")) (List.map (get_oracle_body opt) l))^")"


let impl_init opt p = 
  "let init () ="^
    (file_loading opt ("  "))^
    (translate_process opt p ("  "))
    
let get_interface opt p = 
  let o = List.map (fun (b,n,_,_) -> (b,n)) (get_next_oracles true p) in
  "open Base\n"^
    "open Crypto\n\n"^
  (get_oracles_types p)^"\n"^
    "val init : unit -> "^(get_oracles_type_string o)^"\n"

let get_implementation opt p =
  (!prefix)^
  (get_oracles_types p)^"\n\n"^
    (impl_init opt p)

let impl_translate process opt =
  (get_implementation opt process, get_interface opt process)
