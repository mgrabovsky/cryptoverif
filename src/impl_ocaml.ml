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


(* returns the next oracles. b represents if the oracle is under replication (false) or not (true) *)
let rec get_next_oracles b p =
  match p.i_desc with
    | Nil -> []
    | Input((c,tl),pat,p) ->
        [(b,c.cname,pat,p)]
    | Par (p1,p2) ->
        (get_next_oracles b p1) @ (get_next_oracles b p2)
    | Repl(b,p) -> get_next_oracles false p

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

let get_oracles_types process = 
  "type "^
    string_list_sep "\n and " 
    (StringMap.fold 
       (fun name (s,at) acc -> 
          (get_type_oracle name (s,at))::acc)
       (get_oracle_types_process process) [])

let prefix =
  ref ("open Base\n"^
       "open Crypto\n\n")

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

let do_implementation impl =
  let dir_sep = "/" in
  let impl = impl_check impl in
  List.iter
    (fun (x,opt,p)->
      print_string ("Generating implementation for module "^x^"...\n");
      let (impl, intf) = impl_translate p opt in
      let f = open_out ((!Settings.out_dir)^dir_sep^x^".ml") in
        output_string f impl;
        close_out f;
        let f' = open_out ((!Settings.out_dir)^dir_sep^x^".mli") in
          output_string f' intf;
          close_out f';
          print_string ("Done.\n")
    ) impl

(* vim: set et ts=8 sw=2 tw=0: *)
