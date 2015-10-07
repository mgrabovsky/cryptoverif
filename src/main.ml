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

let front_end_set = ref false

let ends_with s sub =
  let l_s = String.length s in
  let l_sub = String.length sub in
  (l_s >= l_sub) && (String.sub s (l_s - l_sub) l_sub = sub)


(* Prepare the equation statements given by the user *)

let rec get_vars accu t =
  match t.t_desc with
    Var(b,[]) -> 
      if not (List.memq b (!accu)) then 
	accu := b :: (!accu)
  | FunApp(_,l) ->
      List.iter (get_vars accu) l
  | _ -> Parsing_helper.internal_error "statement terms should contain only Var and FunApp\n"

let simplify_statement (vl, t) =
  let glob_reduced = ref false in
  let rec reduce_rec t =
    let reduced = ref false in
    let t' = Terms.apply_eq_reds Terms.simp_facts_id reduced t in
    if !reduced then 
      begin
	glob_reduced := true;
	reduce_rec t'
      end
    else t
  in
  let t' = reduce_rec t in
  if Terms.is_true t' then 
    begin
      print_string "Warning: statement ";
      Display.display_term t;
      print_string " removed using the equational theory.\n"
    end
  else if Terms.is_false t' then
    begin
      print_string "Error: statement ";
      Display.display_term t;
      Parsing_helper.user_error " contradictory.\n"
    end
  else
    let tnew = 
      if !glob_reduced then 
	begin
	  print_string "Statement ";
	  Display.display_term t;
	  print_string " simplified into ";
	  Display.display_term t';
	  print_string " using the equational theory.\n";
	  t'
	  end
      else 
	t
    in
    let record_statement ((_, _, t1, _,t2) as statement) =
      match t1.t_desc with
	FunApp(f, l) -> 
	  f.f_statements <- statement :: f.f_statements
      | _ -> 
	  print_string "Statement ";
	  Display.display_term t1;
	  print_string " = ";
	  Display.display_term t2;
	  print_string " ignored: the left-hand side should start with a function symbol.\n"
    in
    match tnew.t_desc with
      FunApp(f, [t1;t2]) when f.f_cat == Equal ->
	let vars = ref [] in
	get_vars vars t2;
	if not (List.for_all (fun b ->
	  Terms.refers_to b t1
	  ) (!vars)) then
	  begin
	    print_string "Error in simplified statement ";
	    Display.display_term t1;
	    print_string " = ";
	    Display.display_term t2;
	    Parsing_helper.user_error ": all variables of the right-hand side should occur in the left-hand side.\n"
	  end;	  
	record_statement ([], vl, t1, Zero, t2)
    | FunApp(f, [t1;t2]) when f.f_cat == Diff ->
	record_statement ([], vl, tnew, Zero, Terms.make_true());
	record_statement ([], vl, Terms.make_equal t1 t2, Zero, Terms.make_false())
    | _ -> 
	record_statement ([], vl, tnew, Zero, Terms.make_true())
	  
let record_collision ((_, _, t1, _,t2) as collision) =
  match t1.t_desc with
    FunApp(f, l) -> 
      f.f_collisions <- collision :: f.f_collisions
  | _ -> 
      print_string "Collision ";
      Display.display_term t1;
      print_string " <=(...)=> ";
      Display.display_term t2;
      print_string " ignored: the left-hand side should start with a function symbol.\n"

let anal_file s =
  if not (!front_end_set) then
    begin
      (* Use the oracle front-end by default when the file name ends
	 in .ocv *)
      let s_up = String.uppercase s in
      if ends_with s_up ".OCV" then Settings.front_end := Settings.Oracles
    end;
  try
    let (statements, collisions, equivs, move_new_eq, queries, proof, impl, p) = Syntax.read_file s in
    List.iter Check.check_def_eqstatement equivs;
    List.iter (fun (_,eq) -> Check.check_def_eqstatement eq) move_new_eq;
    Check.check_def_process_main p;
    let equivs = List.map Check.check_equiv equivs in
    let new_new_eq = List.map (fun (ty, eq) -> (ty, Check.check_equiv eq)) move_new_eq in
      if !Settings.get_implementation then
        match !Settings.impl_function with
        | Some f -> f impl
        | _ -> Parsing_helper.internal_error "Implementation extraction requested \
                    but no code generation function specified"
      else
        begin
          let g = { proc = Terms.move_occ_process p; game_number = 1; current_queries = [] } in
            let queries =
              if queries == [] then 
	        [(AbsentQuery,g), ref None, None]
              else
	        List.map (fun q -> ((q,g), ref None, None)) queries in
	    g.current_queries <- queries;
            List.iter simplify_statement statements;
            List.iter record_collision collisions;
            Settings.equivs := equivs;
            Settings.move_new_eq := new_new_eq;
            Settings.collect_public_vars queries;
            
            (*
              List.iter Display.display_statement statements;
              print_newline();
              List.iter Display.display_equiv equivs;
              print_newline();
              Display.display_process p;
            *)
            let _ = Instruct.execute_any_crypto proof 
	      { game = g; 
	        prev_state = None } in
              () 
        end
  with End_of_file ->
    print_string "End of file.\n"
    | e ->
        Parsing_helper.internal_error (Printexc.to_string e)

let _ =
  Arg.parse
    [ "-lib", Arg.String (fun s -> Settings.lib_name := s),
      "<filename> \tchoose library file";
      "-tex", Arg.String (fun s -> Settings.tex_output := s),
      "<filename> \tchoose TeX output file";
      "-in", Arg.String (function 
	  "channels" -> Settings.front_end := Settings.Channels
	| "oracles" -> Settings.front_end := Settings.Oracles
	| _ -> Parsing_helper.user_error "Command-line option -in expects argument either \"channels\" or \"oracles\".\n"),
      "channels / -in oracles \tchoose the front-end";
      "-impl", Arg.String (fun s ->
          Settings.get_implementation := true;
          match s with
          | "ocaml"  -> Settings.impl_function := Some Impl_ocaml.do_implementation
          | "python" -> Settings.impl_function := Some Impl_python.do_implementation
          | _ -> Parsing_helper.user_error "Unsupported implementation language\n"),
          "{ocaml,python}\tget implementation of defined modules";
      "-o", Arg.String (fun s -> 
                          try 
                            if (Sys.is_directory s) then Settings.out_dir := s
                            else Parsing_helper.user_error "Command-line option -o expects a directory"
                          with
                              Sys_error _ -> Parsing_helper.user_error "Command-line option -o expects a directory"
                       ),
          "<directory> \tif \"-impl\" is given, the generated files will be placed in this directory (Default: .)";
    ]
    anal_file "Cryptoverif. Cryptographic protocol verifier, by Bruno Blanchet\nCopyright ENS-CNRS, distributed under the CeCILL-B license"
