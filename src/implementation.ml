(*************************************************************
 *                                                           *
 *       Cryptographic protocol verifier                     *
 *                                                           *
 *       Bruno Blanchet and David Cadé                       *
 *                                                           *
 *       Copyright (C) ENS, CNRS, INRIA, 2005-2015           *
 *                     Matěj Grabovský, Red Hat, 2015        *
 *                                                           *
 *************************************************************)

(*

    Copyright ENS, CNRS, INRIA, Red Hat
    contributors: Bruno Blanchet, Bruno.Blanchet@inria.fr
                  David Cadé
                  Matěj Grabovský

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


(* Shortcuts for printing informational messages *)
let info mess = print_string ("Information: "^mess^" (implementation)\n")
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

(*returns set of free and set of bound variables
  get_iprocess_bv returns the set of variables bound not under a replication
  The set of variables bound under a replication is stored in
  bound_vars_under_repl.
  The set of free variables is stored in free_vars. *)
let iprocess_get_vars p =
  free_vars := BinderSet.empty;
  bound_vars_under_repl := BinderSet.empty;
  let bv_no_repl = get_iprocess_bv p in
  let fv = BinderSet.diff (!free_vars) (BinderSet.union bv_no_repl (!bound_vars_under_repl)) in
  let bv_repl = (!bound_vars_under_repl) in
  free_vars := BinderSet.empty;
  bound_vars_under_repl := BinderSet.empty;
  (fv, bv_no_repl, bv_repl)

let oprocess_get_vars p =
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

let get_type_name t =
  match t.timplname with
      Some s -> s
    | None -> error ("Type name required for type "^t.tname)

(* Functions for querying information from implementation annotations *)
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

(* vim: set et ts=8 sw=2 tw=0: *)
