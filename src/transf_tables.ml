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

(* First pass: transform the insert in let calls and return all the created binders *)

let rec transform_insert_iprocess cur_array p =
  match p.i_desc with
    | Nil -> (Terms.iproc_from_desc Nil, [])
    | Par(p1,p2) -> 
        let p1',l1=transform_insert_iprocess cur_array p1 in
        let p2',l2=transform_insert_iprocess cur_array p2 in
          (Terms.iproc_from_desc (Par(p1',p2')),l1@l2)
    | Repl(b,p) ->
        let p',l=transform_insert_iprocess (b::cur_array) p in
          (Terms.iproc_from_desc (Repl(b,p')),l)
    | Input((c,tl),pat,p) ->
        let p',l=transform_insert_oprocess cur_array p in
          (Terms.iproc_from_desc (Input((c,tl),pat,p')),l)

and transform_insert_oprocess cur_array p =
  match p.p_desc with
    | Yield -> (Terms.oproc_from_desc Yield, [])
    | EventAbort f -> (Terms.oproc_from_desc (EventAbort f), [])
    | Restr(b,p) ->
        let p',l=transform_insert_oprocess cur_array p in
          (Terms.oproc_from_desc (Restr(b,p')),l)
    | Test(t,p1,p2) ->
        let p1',l1=transform_insert_oprocess cur_array p1 in
        let p2',l2=transform_insert_oprocess cur_array p2 in
          (Terms.oproc_from_desc (Test(t,p1',p2')),l1@l2)
    | Find(bl,p,fi) ->
        let p',l=transform_insert_oprocess cur_array p in
        let (bl',ll)=List.split (List.map 
                      (fun (bl,d,t,p)->
                         let p'',l'=transform_insert_oprocess cur_array p in
                           ((bl,d,t,p''),l')) bl) in
          (Terms.oproc_from_desc (Find(bl',p',fi)),List.concat (l::ll))
    | Output(c,t,p) ->
        let p',l=transform_insert_iprocess cur_array p in
          (Terms.oproc_from_desc (Output(c,t,p')),l)
    | Let(pat,t,p1,p2) ->
        let p1',l1=transform_insert_oprocess cur_array p1 in
        let p2',l2=transform_insert_oprocess cur_array p2 in
          (Terms.oproc_from_desc (Let(pat,t,p1',p2')),l1@l2)
    | EventP(t,p) ->
        let p',l=transform_insert_oprocess cur_array p in
          (Terms.oproc_from_desc (EventP(t,p')),l)
    | Insert(tbl,tl,p) ->
        Settings.changed := true;
        let p',l=transform_insert_oprocess cur_array p in
        let bl = List.map (fun ty -> Terms.create_binder tbl.tblname (Terms.new_vname()) ty cur_array) tbl.tbltype in
        let p'' = List.fold_right2 (fun b t p ->
                                      Terms.oproc_from_desc (Let(PatVar(b),t,p,Terms.oproc_from_desc Yield))
                                   ) bl tl p' in
          (p'',(tbl,Some bl)::l)
    | Get(tbl,patl,topt,p1,p2) ->
        let p1',l1=transform_insert_oprocess cur_array p1 in
        let p2',l2=transform_insert_oprocess cur_array p2 in
          (Terms.oproc_from_desc (Get(tbl,patl,topt,p1',p2')),(tbl,None)::(l1@l2))

let transform_insert p = 
  transform_insert_iprocess [] p

(* Second pass: transform the Get calls into Find calls *)

let rec get_info_for tbl = function
    [] -> []
  | (tbl', Some i)::r when tbl == tbl' -> i::(get_info_for tbl r)
  | _::r -> get_info_for tbl r

let rec get_find_branch_term brl patl t =
  match brl,patl with 
    | [],[] -> t
    | [],_ | _,[] -> Parsing_helper.internal_error "get_find_branch_term: lists not of the same size"
    | br::brl',pat::patl' ->
        let t1=Terms.term_from_binderref br in
          (match pat with
            | PatVar (b) -> 
               let subst = Terms.OneSubst(b,t1,ref false) in
               let patl'' = List.map (Terms.copy_pat subst) patl' in
               let t' = Terms.copy_term subst t in
                 get_find_branch_term brl' patl'' t'
            | PatEqual (t2) -> 
                let t' = get_find_branch_term brl' patl' t in
                  Terms.make_and (Terms.make_equal t1 t2) t'
            | PatTuple _ ->
                let t' = get_find_branch_term brl' patl' t in
                  Terms.build_term_type Settings.t_bool 
                    (LetE(pat, t1, t', Some (Terms.make_false ()))))

let rec get_find_branch_process brl patl p =
  match brl,patl with 
    | [],[] -> p
    | [],_ | _,[] -> Parsing_helper.internal_error "get_find_branch_process: lists not of the same size"
    | br::brl',pat::patl' ->
        let t1=Terms.term_from_binderref br in
        (match pat with
           | PatVar (b) ->
	       let subst = Terms.OneSubst(b,t1,ref false) in
	       let patl'' = List.map (Terms.copy_pat subst) patl' in
	       let p' = Terms.copy_oprocess subst p in
               get_find_branch_process brl' patl'' p'
           | PatEqual (t2) ->
               (* at this point, this is always true *)
               get_find_branch_process brl' patl' p
           | _ ->
               let p' = get_find_branch_process brl' patl' p in
                 Terms.oproc_from_desc (Let(pat, t1, p', Terms.oproc_from_desc Yield)))

let get_find_branch patl topt p cur_array bl =
  let ac = (List.hd bl).args_at_creation in
  let vars = List.map (fun a -> Terms.create_binder "u" (Terms.new_vname ()) a.ri_type cur_array) ac in
  let vars_t = List.map Terms.term_from_binder vars in
  let repl_indices = List.map (fun a -> Terms.create_repl_index "u" (Terms.new_vname ()) a.ri_type) ac in
  let repl_indices_t = List.map Terms.term_from_repl_index repl_indices in
  let brl = List.map (fun b -> (b,repl_indices_t)) bl in
  let t = get_find_branch_term brl patl (match topt with None -> Terms.make_true () | Some t -> t) in
  let brl' = List.map (fun b -> (b,vars_t)) bl in
  let p' = get_find_branch_process brl' patl p in
  (List.combine vars repl_indices,brl,
   Terms.update_args_at_creation (repl_indices @ cur_array) t,p')

let rec transform_get_iprocess l cur_array p =
  Terms.iproc_from_desc (
    match p.i_desc with
      | Nil -> Nil
      | Par(p1,p2) -> 
          let p1'=transform_get_iprocess l cur_array p1 in
          let p2'=transform_get_iprocess l cur_array p2 in
            Par(p1',p2')
      | Repl(b,p) ->
          let p'=transform_get_iprocess l (b::cur_array) p in
            Repl(b,p')
      | Input((c,tl),pat,p) ->
          let p'=transform_get_oprocess l cur_array p in
            Input((c,tl),pat,p'))

and transform_get_oprocess l cur_array p =
  Terms.oproc_from_desc (
    match p.p_desc with
      | Yield -> Yield
      |	EventAbort f -> EventAbort f
      | Restr(b,p) ->
          let p'=transform_get_oprocess l cur_array p in
            Restr(b,p')
      | Test(t,p1,p2) ->
          let p1'=transform_get_oprocess l cur_array p1 in
          let p2'=transform_get_oprocess l cur_array p2 in
            Test(t,p1',p2')
      | Find(l0,p,fi) ->
          let p'=transform_get_oprocess l cur_array p in
          let l0'=List.map 
            (fun (bl,d,t,p)->
               let p''=transform_get_oprocess l cur_array p in
                 (bl,d,t,p'')) l0 in
            Find(l0',p',fi)
      | Output(c,t,p) ->
          let p'=transform_get_iprocess l cur_array p in
            Output(c,t,p')
      | Let(pat,t,p1,p2) ->
          let p1'=transform_get_oprocess l cur_array p1 in
          let p2'=transform_get_oprocess l cur_array p2 in
            Let(pat,t,p1',p2')
      | EventP(t,p) ->
          let p'=transform_get_oprocess l cur_array p in
            EventP(t,p')
      | Insert(tbl,tl,p) ->
          let p'=transform_get_oprocess l cur_array p in
            Insert(tbl,tl,p')
      | Get(tbl,patl,topt,p1,p2) ->
          Settings.changed := true;
          let p1'=transform_get_oprocess l cur_array p1 in
          let p2'=transform_get_oprocess l cur_array p2 in
          Find (List.map (get_find_branch patl topt p1' cur_array) (get_info_for tbl l), p2', Nothing)
  )
          
let transform_get p l =
  transform_get_iprocess l [] p

let reduce_tables g =
  Terms.array_ref_process g.proc;
  let (p,l) = transform_insert g.proc in
  let tables = ref [] in
  List.iter (fun (tbl,_) ->
    if not (List.memq tbl (!tables)) then tables := tbl :: (!tables)) l;
  let g1 = { proc = transform_get p l; game_number = -1; current_queries = g.current_queries } in
  Terms.cleanup_array_ref();
  let (g', proba, renames) = Transf_auto_sa_rename.auto_sa_rename g1 in
  (g', proba, renames @ (List.map (fun tbl -> DExpandGetInsert tbl) (!tables)))


