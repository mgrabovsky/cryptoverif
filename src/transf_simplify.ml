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
open Simplify1

let whole_game = ref { proc = Terms.iproc_from_desc Nil; game_number = -1; current_queries = [] }

let current_pass_transfos = ref []

(* Priorities for orienting equalities into rewrite rules *)
let current_max_priority = ref 0
let priority_list = ref []

let proba_state_at_beginning_iteration = ref (([],[]), [])
let failure_check_all_deps = ref []

(* Initialization of probability counting *)  

let partial_reset g = 
  whole_game := g;
  (* Remove the advice found in Transf_globaldepanal in previous iterations. 
     If advice is still useful, we will find it again at the next iteration. *)
  Transf_globaldepanal.advise := [];
  proba_state_at_beginning_iteration := (Proba.get_current_state(), !term_collisions);
  failure_check_all_deps := [];
  current_max_priority := 0;
  List.iter (fun b -> b.priority <- 0) (!priority_list);
  priority_list := []

let reset coll_elim g =
  partial_reset g;
  Simplify1.reset coll_elim g;

(* Dependency analysis
   When M1 characterizes a part of x of a large type T
   and M2 does not depend on x, then M1 = M2 fails up to
   negligible probability.
   The module FindCompos defines "characterize"
   The modules Transf_globaldepanal and DepAnal2 perform dependency analyses
   Function dependency_collision concludes *)

module DepAnal2 :
sig
(* Local dependency analysis: take into account the freshness
   of the random number b to determine precisely which expressions depend on b
   for expressions defined before the first output that follows the choice
   of b *)

  type dep_info 
  type elem_dep_info = (typet * term) FindCompos.depinfo
  (* The dependency information [dep_info] contains a list of
     [(b, (dep, nodep))] that associates to each variable [b]
     its dependency information [(dep,nodep)] of type [elem_dep_info]. 

     [dep] is 
     - either [None], when any variable may depend on [b];
     - or [Some l], where [l] is a list variables [b'] that depend on [b], 
     with their associated status, the type of the part of [b] 
     that [b'] characterizes, and a term that describes how to 
     compute [b'] from [b].
     The status is
      * [Compos] when [b'] is obtained from [b] by first applying
        poly-injective functions (functions marked [compos]), then
        functions that extract a part of their argument 
        (functions marked [uniform]).
      * [Decompos] when [b'] is obtained from [b] by applying functions
        that extract a part of their argument (functions marked [uniform])
      * [Any] in the other cases
     It is guaranteed that only the variables in [l] depend on [b].
     [nodep] is a list of terms that do not depend on [b[b.args_at_creation]] *)

  (* [init] is the empty dependency information *)
  val init : dep_info

  (* find_compos_glob depinfo b t   returns Some ty when
     t characterizes a part of b of type ty, knowing the dependency
     information given in depinfo. Otherwise, returns None. *)
  val find_compos_glob : elem_dep_info -> binder -> term -> (typet * term) option

  (* [update_dep_info] and [update_dep_infoo] update the dependency information
     inside processes.

     [update_dep_info cur_array dep_info true_facts p] returns the dependency information
     valid at the immediate subprocesses of [p] when [p] is an input process. The dependency
     information is the same for all subprocesses of [p], and is actually equal to the
     dependency information for [p] itself.

     [update_dep_infoo cur_array dep_info true_facts p] returns a simplified version [p']
     of process [p] (using the dependency information), as well as the dependency information
     valid at the immediate subprocesses of [p'] when [p] is an output process. There is
     one dependency information for each immediate subprocess of [p'] (e.g. 2 for "if",
     one for the "then" branch and one for the "else" branch; one for each branch of "find",
     and so on).

     [cur_array] is the list of current replication indices.
     [dep_info] is the dependency information valid at [p].
     [true_facts] are facts that are known to hold at [p]. *)
  val update_dep_info : repl_index list -> dep_info -> simp_facts -> inputprocess -> dep_info
  val update_dep_infoo : repl_index list -> dep_info -> simp_facts -> process -> process * dep_info list 

  (* [get_dep_info dep_info b] extracts from [dep_info] the
     dependency information of the variable [b]. *)
  val get_dep_info : dep_info -> binder -> elem_dep_info

  (* [is_indep (b, depinfo) t] returns a term independent of [b]
     in which some array indices in [t] may have been replaced with
     fresh replication indices. When [t] depends on [b] by variables
     that are not array indices, it raises [Not_found] *)
  val is_indep : (binder * elem_dep_info) -> term -> term
end
= 
struct

open FindCompos

type elem_dep_info = (typet * term) FindCompos.depinfo
type dep_info = (binder * elem_dep_info) list
      (* list of [(b, (dep, nodep))], where 
     [dep] is 
     - either [Some l], where [l] is a list variables [b'] that depend on [b], 
     with their associated "find_compos" status, the type of the part of [b] 
     that [b'] characterizes, and a term that describes how to 
     compute [b'] from [b];
     - or [None], when any variable may depend on [b].
     [nodep] is a list of terms that do not depend on [b[b.args_at_creation]] *)

let init = []

let depends = FindCompos.depends

let is_indep = FindCompos.is_indep
    
(* find_compos b t returns true when t characterizes b: only one
value of b can yield a certain value of t *)

let check (b, (st, (bct, _))) l =
  if Terms.is_args_at_creation b l then
    Some (st, CharacType bct)
  else
    None

let find_compos_list ((b, (dep, nodep)) as var_depinfo) t =
  let seen_list' = match dep with
    Some seen_list -> seen_list
  | None -> [(b,(Decompos, (b.btype, Terms.term_from_binder b)))]
  in
  match FindCompos.find_compos_list check var_depinfo seen_list' t with
    Some(st, CharacType charac_type, t', b', (_,assign)) -> Some(st, charac_type, t', b', assign)
  | Some _ -> Parsing_helper.internal_error "CharacTypeOfVar should not be used in DepAnal2"
  | None -> None

let find_compos_glob depinfo b t =
  match FindCompos.find_compos check (b, depinfo) (b,(Decompos, (b.btype, Terms.term_from_binder b))) t with
    Some(_, CharacType charac_type, t') -> Some(charac_type, t')
  | Some _ -> Parsing_helper.internal_error "CharacTypeOfVar should not be used in DepAnal2"
  | None -> None

let subst b t t' =
  Terms.copy_term (Terms.OneSubst(b,t,ref false)) t'

exception Else

(* checkassign1 is called when the assigned term depends on b with status st
   Raises Else when only the else branch of the let may be taken *)
let rec check_assign1 cur_array true_facts ((t1, t2, b, charac_type) as proba_info) bdep_info st pat =
  match pat with
    PatVar _ -> ()
  | PatTuple(f,l) ->
      let st' = if st != Decompos then Any else st in
      List.iter (check_assign1 cur_array true_facts proba_info bdep_info st') l
  | PatEqual t ->
      if (depends bdep_info t) || 
        (not (Proba.is_large_term t)) || (st == Any) then
	()
      else
	begin
	  (* add probability *)
	  if add_term_collisions (cur_array, true_facts_from_simp_facts true_facts, [], Terms.make_true()) 
	      t1 t2 b (Some (List.map Terms.term_from_repl_index b.args_at_creation)) [charac_type] then
	    raise Else
	end

(* check_assign2 is called when the assigned term does not depend on b
   Return None when both branches may be taken and
          Some(charac_type, t') when only the else branch of the let
          may be taken. t' is the term with which the collision is
          eliminated and charac_type is the type of the part of t'
          characterized by the value of t' *)
let rec check_assign2 bdepinfo = function
    PatVar _ ->
      None
  | PatTuple(f,l) ->
      begin
        match check_assign2_list bdepinfo l with
	  None -> None
	| Some(charac_type, l') ->
	    Some(charac_type, Terms.build_term_type (snd f.f_type) (FunApp(f,l')))
      end
  | PatEqual t ->
      match find_compos_list bdepinfo t with
	Some (status, charac_type, t', b2, b2fromb) when Proba.is_large_term t ->
	  Some (charac_type, subst b2 b2fromb t')
      |	_ ->
	  None

and check_assign2_list bdepinfo = function
    [] -> None
  | (a::l) ->
      match check_assign2 bdepinfo a with
	None -> 
	  begin
	    match check_assign2_list bdepinfo l with
	      None -> None
	    | Some(charac_type, l') -> Some(charac_type, (any_term_pat a)::l')
	  end
      |	Some(charac_type, a') -> Some(charac_type, a'::(List.map any_term_pat l))
      
let rec remove_dep_array_index_pat bdepinfo = function
    PatVar b -> PatVar b
  | PatTuple(f,l) ->
      PatTuple(f, List.map (remove_dep_array_index_pat bdepinfo) l)
  | PatEqual t ->
      PatEqual (FindCompos.remove_dep_array_index bdepinfo t)

let rec depends_pat bdepinfo = function
    PatVar _ ->
      false
  | PatTuple(f,l) ->
      List.exists (depends_pat bdepinfo) l
  | PatEqual t ->
      depends bdepinfo t

let rec simplify_term cur_array dep_info true_facts t =
  match t.t_desc with
    FunApp(f,[t1;t2]) when f == Settings.f_and ->
      (* We simplify t2 knowing t1 and t1 knowing t2, by swapping the "and"
         after the simplification of t2 *)
      begin
	try
	  let true_facts2 = Facts.simplif_add Facts.no_dependency_anal true_facts t1 in
	  let t2' = simplify_term cur_array dep_info true_facts2 t2 in
	  let true_facts1 = Facts.simplif_add Facts.no_dependency_anal true_facts t2' in
	  Terms.make_and (simplify_term cur_array dep_info true_facts1 t1)  t2'
	with Contradiction ->
	  Terms.make_false()
      end
  | FunApp(f,[t1;t2]) when f == Settings.f_or ->
      (* We simplify t2 knowing (not t1) and t1 knowing (not t2), 
	 by swapping the "or" after the simplification of t2 *)
      begin
	try
	  let true_facts2 = Facts.simplif_add Facts.no_dependency_anal true_facts (Terms.make_not t1) in
	  let t2' = simplify_term cur_array dep_info true_facts2 t2 in
	  let true_facts1 = Facts.simplif_add Facts.no_dependency_anal true_facts (Terms.make_not t2') in
	  Terms.make_or (simplify_term cur_array dep_info true_facts1 t1) t2' 
	with Contradiction ->
	  Terms.make_true()
      end
  | FunApp(f,[t1]) when f == Settings.f_not ->
      let t' = simplify_term cur_array dep_info true_facts t1 in
      if Terms.is_false t' then Terms.make_true() else
      if Terms.is_true t' then Terms.make_false() else
      Terms.make_not t'
  | FunApp(f,[t1;t2]) 
    when ((f.f_cat == Equal) || (f.f_cat == Diff)) && (Proba.is_large_term t1 || Proba.is_large_term t2) ->
      begin
	let rec try_dep_info = function
	    [] -> t
	  | ((b, _) as bdepinfo)::restl ->
	      let t1' = remove_dep_array_index bdepinfo t1 in
	      match find_compos_list bdepinfo t1' with
		Some(_, charac_type, t1'', b2, b2fromb) ->
		  begin
		    try 
		      let t2' = is_indep bdepinfo t2 in
                      (* add probability; if too large to eliminate collisions, raise Not_found *)
		      if not (add_term_collisions (cur_array, true_facts_from_simp_facts true_facts, [], Terms.make_true()) (subst b2 b2fromb t1'') t2' b (Some (List.map Terms.term_from_repl_index b.args_at_creation)) [charac_type]) then raise Not_found;
		      if (f.f_cat == Diff) then Terms.make_true() else Terms.make_false()
		    with Not_found ->
		      try_dep_info restl
		  end
	      | None -> 
		  let t2' = remove_dep_array_index bdepinfo t2 in
		  match find_compos_list bdepinfo t2' with
		  Some(_,charac_type, t2'', b2, b2fromb) ->
		    begin
		      try 
			let t1' = is_indep bdepinfo t1 in
                        (* add probability; if too large to eliminate collisions, raise Not_found *)
			if not (add_term_collisions (cur_array, true_facts_from_simp_facts true_facts, [], Terms.make_true()) (subst b2 b2fromb t2'') t1' b (Some (List.map Terms.term_from_repl_index b.args_at_creation)) [charac_type]) then raise Not_found;
			if (f.f_cat == Diff) then Terms.make_true() else Terms.make_false()
		      with Not_found ->
			try_dep_info restl
		    end
		| None ->
		    try_dep_info restl
	in
	try_dep_info dep_info
      end
  | _ -> t

(* Takes a dep_info as input and returns the new dep_info for the subprocesses
   of the input process p *)

let update_dep_info cur_array dep_info true_facts p = dep_info

(* Takes a dep_info as input and returns a simplified process and
   the list of new dep_info's for the subprocesses *)

let rec update_dep_infoo cur_array dep_info true_facts p' = 
  match p'.p_desc with
    Yield -> (Terms.oproc_from_desc2 p' Yield, [])
  | EventAbort f -> (Terms.oproc_from_desc2 p' (EventAbort f), [])
  | Restr(b,p) ->
      let b_term = Terms.term_from_binder b in
      let dep_info' = List.map (fun (b', (dep, nodep)) -> (b', (dep, b_term::nodep))) dep_info in
      if Proba.is_large b.btype then
	try 
	  let def_vars = Facts.get_def_vars_at p'.p_facts in
	  (Terms.oproc_from_desc (Restr(b,p)), 
	   [(b, (Some [b, (Decompos, (b.btype, Terms.term_from_binder b))], 
		 (List.map Terms.term_from_binderref def_vars))) :: dep_info' ])
	with Contradiction ->
	  (* The current program point is unreachable, because it requires the definition
	     of a variable that is never defined *)
	  (Terms.oproc_from_desc2 p' Yield, [])
      else
	(Terms.oproc_from_desc2 p' (Restr(b,p)), [dep_info'])
  | Test(t,p1,p2) ->
      let t' = simplify_term cur_array dep_info true_facts t in
      if Terms.is_true t' then
	begin
	  Settings.changed := true;
	  current_pass_transfos := (STestTrue(p')) :: (!current_pass_transfos);
	  update_dep_infoo cur_array dep_info true_facts p1
	end
      else if Terms.is_false t' then
	begin
	  Settings.changed := true;
	  current_pass_transfos := (STestFalse(p')) :: (!current_pass_transfos);
	  update_dep_infoo cur_array dep_info true_facts p2
	end
      else
	let r = List.map (function ((b, (dep, nodep)) as bdepinfo) ->
	  if depends bdepinfo t' then
	    (b, (None, nodep))
	  else
	    bdepinfo) dep_info
	in
	if not (Terms.equal_terms t t') then 
	  begin
	    Settings.changed := true;
	    current_pass_transfos := (SReplaceTerm(t,t')) :: (!current_pass_transfos);
	  end;
	(Terms.oproc_from_desc2 p' (Test(t',p1,p2)), [r])
  | Find(l0,p2,find_info) ->
       let always_then = ref false in
       let rec simplify_find = function
          [] -> []
        | (bl, def_list, t, p1)::l ->
            let l' = simplify_find l in
	    let bl'' = List.map snd bl in
            let t' = simplify_term (bl'' @ cur_array) dep_info true_facts t
            in
            if Terms.is_false t' then 
	      begin
		Settings.changed := true;
		current_pass_transfos := (SFindBranchRemoved(p', (bl, def_list, t, p1))) :: (!current_pass_transfos);
		l'
	      end 
	    else 
	      begin
		if Terms.is_true t' && def_list == [] then always_then := true;
		if not (Terms.equal_terms t t') then Settings.changed := true;
		(bl, def_list, t', p1)::l'
	      end
       in
       let l0' = simplify_find l0 in
       begin
	 match l0' with
	   [] -> 
	     Settings.changed := true;
             update_dep_infoo cur_array dep_info true_facts p2
	 | [([],[],t, p1)] when Terms.is_true t ->
	     Settings.changed := true;
	     current_pass_transfos := (SFindElseRemoved(p')) :: (!current_pass_transfos);
	     update_dep_infoo cur_array dep_info true_facts p1
	 | _ ->
         (* For each b in dep_info.in_progress, does the branch taken
            depend on b? *)
         let dep_b = List.map (fun bdepinfo ->
	   let tmp_bad_dep = ref false in
	   let check_br (b, l) = 
	     if List.exists (depends bdepinfo) l then tmp_bad_dep := true
	   in
	   List.iter (fun (bl, def_list, t, p1) ->
	     List.iter check_br def_list;
	     if depends bdepinfo t then tmp_bad_dep := true;
		  ) l0';
           !tmp_bad_dep) dep_info 
	 in

         (* Dependence info for the "then" branches *)
         let dep_info_branches = List.fold_right (fun (bl, def_list, _, _) accu ->
	   let this_branch_node = Facts.get_node p'.p_facts in
	   (* Variables that are certainly defined before the find do not depend on b *)
	   let nodep_add_cond = List.map Terms.term_from_binderref 
	     (try
	       Facts.def_vars_from_defined this_branch_node def_list
	     with Contradiction -> 
	       (* For simplicity, I ignore when a variable can in fact not be defined. 
		  I could remove that branch of the find to be more precise *)
	       def_list)
	       (* I add variables by closing recursively variables
	          that must be defined *)
	   in
	   (* nodep_add_then is the same as nodep_add_cond, except that
	      the replication indices of find are replaced with the corresponding variables. *)
	   let nodep_add_then = List.map (Terms.subst (List.map snd bl) 
	       (List.map (fun (b,_) -> Terms.term_from_binder b) bl)) nodep_add_cond 
	   in
	   (* Dependence info for the condition *)
	   let dep_info_cond = 
	     List.map (fun ((b, (dep, nodep)) as bdepinfo) ->
	       (b, (dep, (List.filter (fun t -> not (depends bdepinfo t)) nodep_add_cond) @ nodep))
		 ) dep_info
	   in
	   (* Dependence info for the then branch.
	      The replication indices of find are replaced with the corresponding variables. *)
	   let dep_info_then = 
	     List.map2 (fun dep1 ((b, (dep, nodep)) as bdepinfo) ->
	       if dep1 then
		 (b, (None, nodep))
	       else
		 (b, (dep, (List.filter (fun t -> not (depends bdepinfo t)) nodep_add_then) @ nodep))
		   ) dep_b dep_info
	   in
	   dep_info_cond :: dep_info_then :: accu
             ) l0' []
	 in
         (* Dependence info for the else branch *)
	 let dep_info_else = List.map2 
	     (fun dep1 ((b, (dep, nodep)) as bdepinfo) ->
	       if dep1 then
		 (b, (None, nodep))
	       else
		 bdepinfo) dep_b dep_info
	 in
         (Terms.oproc_from_desc2 p' (Find(l0',(if !always_then then Terms.oproc_from_desc Yield else p2), find_info)), dep_info_else :: dep_info_branches)
       end
  | Let(pat, t, p1, p2) ->
      begin
        match pat with
          PatVar b' -> 
            let dep_info' = 
              List.map (fun ((b, (dep, nodep)) as bdepinfo) ->
		if depends bdepinfo t then
		  match dep with
		    None -> bdepinfo
		  | Some dl ->
                      match find_compos_list bdepinfo t with
	                Some (st, charac_type, t', b2, b2fromb) -> 
			  (b, (Some ((b',(st, (charac_type, subst b2 b2fromb t')))::dl), nodep))
                      | None -> 
			  let rec find_dep = function
			      [] -> 
				Parsing_helper.internal_error "t does not depend on b; this should have been detected by depends before"
                                (*(b, (dep, (Terms.term_from_binder b')::nodep))*)
			    | (b2, (_, (_, b2fromb)))::dep' ->
				if Terms.refers_to b2 t then
				  (b, (Some ((b', (Any, (b.btype, subst b2 b2fromb t)))::dl), nodep))
				else
				  find_dep dep'
			  in
			  find_dep dl
		else
		  (b, (dep, (Terms.term_from_binder b')::nodep))
                 ) dep_info 
            in
	    if p2.p_desc != Yield then 
	      begin
		Settings.changed := true;
		current_pass_transfos := (SLetElseRemoved(p')) :: (!current_pass_transfos);
	      end;
            (Terms.oproc_from_desc2 p' (Let(pat, t, p1, Terms.oproc_from_desc Yield)), [dep_info'])
        | _ -> 
            let bl = Terms.vars_from_pat [] pat in
            let bl_terms = List.map Terms.term_from_binder bl in
	    try        
	      (* status is true when the chosen branch may depend on b *)
              let status ((b, _) as bdepinfo) =
		let t' = FindCompos.remove_dep_array_index bdepinfo t in
		let pat' = remove_dep_array_index_pat bdepinfo pat in
		match find_compos_list bdepinfo t' with
		  Some (st, charac_type, t'', b2, b2fromb) ->
		    check_assign1 cur_array true_facts (subst b2 b2fromb t'', Terms.term_from_pat pat', b, charac_type) bdepinfo st pat';
		    true
		| None ->
		    begin
		      if depends bdepinfo t' then () else
		      match check_assign2 bdepinfo pat' with
			None -> ()
		      |	Some(charac_type, t1') ->
			  (* Add probability *)
			  if add_term_collisions (cur_array, true_facts_from_simp_facts true_facts, [], Terms.make_true()) t1' t' b (Some (List.map Terms.term_from_repl_index b.args_at_creation)) [charac_type] then
			    raise Else
		    end;
		    (depends bdepinfo t) || (depends_pat bdepinfo pat)
	      in
	      (* dependency information for the "in" and "else" branches *)
	      let dep_info' = List.map (fun ((b, (dep, nodep)) as bdepinfo) ->
		if status bdepinfo then
		  (b, (None, nodep)), (b, (None, nodep))
		else
		  (b, (dep, bl_terms @ nodep)), bdepinfo
		    ) dep_info
	      in
	      let dep_info1, dep_info2 = List.split dep_info' in
              (Terms.oproc_from_desc2 p' (Let(pat, t, p1, p2)), [dep_info1; dep_info2])
	    with Else ->         
	      Settings.changed := true;
	      current_pass_transfos := (SLetRemoved(p')) :: (!current_pass_transfos);	      
	      update_dep_infoo cur_array dep_info true_facts p2
      end
  | Output _ ->
      (p', [List.map (fun (b, (dep, nodep)) -> (b, (None, nodep))) dep_info])
  | EventP _ ->
      (p', [dep_info])
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

  let get_dep_info dep_info b =
    try 
      List.assq b dep_info
    with Not_found ->
      (None, []) (* Not found *)

end (* Module DepAnal2 *)

(* The exception [Restart(b,g)] is raised by [dependency_collision_rec1]
   when simplification should be restarted on the game [g] 
   obtained by a successful global dependency analysis 
   on binder [b]. *) 
exception Restart of binder * game

(* The functions [dependency_collision_rec1], [dependency_collision_rec2],
   and [dependency_collision_rec3] have similar interfaces.
   They all aim to simplify [t1 = t2] by eliminating collisions
   using dependency analyses.
   [dependency_collision_rec1] uses the global dependency analysis 
   (module [Transf_globaldepanal]).
   [dependency_collision_rec2] uses the local dependency analysis
   (module [DepAnal2]).
   [dependency_collision_rec3] just uses that randomly chosen values
   do not depend on other variables.
   Basically, the collision is eliminated when [t1] characterizes
   a large part of a random variable [b] and [t2] does not depend 
   on [b]. 
   [t] is a subterm of [t1] that contains the variable [b].
   (Initially, it is [t1], and recursive calls are made until [t] is 
   just a variable.)

   They return [None] when they fail, and [Some t'] when they
   succeed in simplifying [t1=t2] into [t'], except [dependency_collision_rec1]
   which raises exception [Restart] so that the simplification
   is restarted on the game after dependency analysis.

   [cur_array] is the list of current replication indices.
   [true_facts] is a list of facts that are known to hold.
   For [dependency_collision_rec2], [depinfo] contains the local
   dependency information. *)

let rec dependency_collision_rec1 cur_array true_facts t1 t2 t =
  match t.t_desc with
    Var(b,l) when (Terms.is_restr b) && (Proba.is_large_term t) && (not (Terms.refers_to b t2)) ->
      begin
	let check (b, (st, _)) l' = 
	  if List.for_all2 Terms.equal_terms l' l then
	    Some (st, FindCompos.CharacTypeOfVar b) 
	  else
	    None
	in
	match FindCompos.find_compos check (b,(None, [])) (b,(FindCompos.Decompos, ref [FindCompos.CharacType b.btype])) t1 with
	  None -> None
	| Some _ -> 
	    if List.memq b (!failure_check_all_deps) then None else
	    begin
	      print_string "Doing global dependency analysis on ";
	      Display.display_binder b;
	      print_string " inside simplify... "; flush stdout;
	      let current_proba_state = Proba.get_current_state() in
	      let current_term_collisions = !term_collisions in
	      match Transf_globaldepanal.check_all_deps b (!proba_state_at_beginning_iteration) (!whole_game) with
		None -> 
		  (* global dependency analysis failed *)
		  print_string "No change"; print_newline();
		  Proba.restore_state current_proba_state;
		  term_collisions := current_term_collisions;
		  failure_check_all_deps := b :: (!failure_check_all_deps);
		  None
	      | Some(res_game) ->
		  (* global dependency analysis succeeded. 
                     Restart simplification from the result of global dep anal *)
		  print_string "Done. Restarting simplify"; print_newline();
		  Settings.changed := true;
		  raise (Restart(b, res_game))
	    end
      end
  | FunApp(f,l) ->
      Terms.find_some (dependency_collision_rec1 cur_array true_facts t1 t2) l
  | _ -> None

(* [is_indep ((b0,l0,(dep,nodep),collect_bargs,collect_bargs_sc) as bdepinfo) t] 
   returns a term independent of [b0[l0]] in which some array indices in [t] 
   may have been replaced with fresh replication indices. 
   When [t] depends on [b0[l0]] by variables that are not array indices, it raises [Not_found].
   [(dep,nodep)] is the dependency information:
     [dep] is either [Some dl] when only the variables in [dl] may depend on [b0]
              or [None] when any variable may depend on [b0];
     [nodep] is a list of terms that are known not to depend on [b0].
   [collect_bargs] collects the indices of [b0] (different from [l0]) on which [t] depends
   [collect_bargs_sc] is a modified version of [collect_bargs] in which  
   array indices that depend on [b0] are replaced with fresh replication indices
   (as in the transformation from [t] to the result of [is_indep]). *)

let rec is_indep ((b0,l0,(dep,nodep),collect_bargs,collect_bargs_sc) as bdepinfo) t =
  Terms.build_term2 t
     (match t.t_desc with
	FunApp(f,l) -> FunApp(f, List.map (is_indep bdepinfo) l)
      | ReplIndex(b) -> t.t_desc
      |	Var(b,l) ->
	  if (List.exists (Terms.equal_terms t) nodep) then
	    t.t_desc 
	  else if (b != b0 && Terms.is_restr b) || (match dep with
	      None -> false
	    | Some dl -> not (List.exists (fun (b',_) -> b' == b) dl))
	  then
	    Var(b, List.map (fun t' ->
	      try
		is_indep bdepinfo t'
	      with Not_found ->
		Terms.term_from_repl_index (Simplify1.new_repl_index_term t')) l)
	  else if b == b0 then
	    if List.for_all2 Terms.equal_terms l0 l then
	      raise Not_found 
	    else 
	      begin
		let l' = 
		  List.map (fun t' ->
		  try
		    is_indep bdepinfo t'
		  with Not_found ->
		    Terms.term_from_repl_index (Simplify1.new_repl_index_term t')) l
		in
		if not (List.exists (List.for_all2 Terms.equal_terms l) (!collect_bargs)) then
		  begin
		    collect_bargs := l :: (!collect_bargs);
		    collect_bargs_sc := l' :: (!collect_bargs_sc)
		  end;
		Var(b, l')
	      end
	  else
	    raise Not_found
      | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in is_indep")
    
let rec dependency_collision_rec2 cur_array true_facts dep_info t1 t2 t =
  match t.t_desc with
    Var(b,l) when (Terms.is_restr b) && (Proba.is_large_term t) && (Terms.is_args_at_creation b l) ->
      begin
	 let depinfo = DepAnal2.get_dep_info dep_info b in
	 let t1' = FindCompos.remove_dep_array_index (b,depinfo) t1 in
	 match DepAnal2.find_compos_glob depinfo b t1' with
	   None -> None
	 | Some(charac_type, t1'') ->
	    try 
	      let collect_bargs = ref [] in
	      let collect_bargs_sc = ref [] in
	      let t2' = is_indep (b,l,depinfo,collect_bargs,collect_bargs_sc) t2 in
	      (* We eliminate collisions because t1 characterizes b[l] and t2 does not depend on b[l],
                 In case b occurs in t2, we reason as follows:
                    1/ When the indices of b in t2 are all different from l, t2 does not depend on b[l].
                       We eliminate collisions under that additional condition, hence the equality 
                       t1 = t2 is false in this case.
                       We collect in collect_bargs the indices l_i of b in t2. Hence the additional
                       condition is &&_(l_i in collect_bargs) l <> l_i. This condition is added
                       as side_condition below.
                    2/ Therefore, we can replace t1 = t2 with 
	               (t1 = t2) && (||_(l_i in collect_bargs) l = l_i),
	               which we rewrite
                       ||_(l_i in collect_bargs) (l = l_i && t1 = t2 { l/l_i }) 
		 *)
	      let side_condition = 
		Terms.make_and_list (List.map (fun l' ->
		  Terms.make_or_list (List.map2 Terms.make_diff l l')
		    ) (!collect_bargs_sc))
	      in
	      (* add probability; returns true if small enough to eliminate collisions, false otherwise. *)
	      if add_term_collisions (cur_array, true_facts, [], side_condition) t1'' t2' b (Some (List.map Terms.term_from_repl_index b.args_at_creation)) [charac_type] then
		Some (Terms.make_or_list (List.map (fun l' ->   
		  let t2'' = Terms.replace l' l t2 in
		    Terms.make_and (Terms.make_and_list (List.map2 Terms.make_equal l l')) (Terms.make_equal t1 t2'')
		    ) (!collect_bargs)))
              else
                None
	    with Not_found -> None
      end 
  | FunApp(f,l) ->
      Terms.find_some (dependency_collision_rec2 cur_array true_facts dep_info t1 t2) l
  | _ -> None

let rec dependency_collision_rec3 cur_array true_facts t1 t2 t =
  let t_simp_ind = FindCompos.remove_array_index t in
  match t_simp_ind.t_desc, t.t_desc with
    Var(b,l_simp_ind), Var(b',l) when (Terms.is_restr b) && (Proba.is_large_term t) ->
      assert (b == b');
      begin
	let t1_simp_ind = FindCompos.remove_array_index t1 in
	let check (b, (st, _)) tl =
	  if List.for_all2 Terms.equal_terms tl l_simp_ind then
	    Some (st, FindCompos.CharacType b.btype) 
	  else 
	    None
	in
	match FindCompos.find_compos check (b,FindCompos.init_elem) (b, (FindCompos.Decompos, b.btype)) t1_simp_ind with
	  Some(_, FindCompos.CharacType charac_type, t1') -> 
	    begin
	      try 
		let collect_bargs = ref [] in
		let collect_bargs_sc = ref [] in
		let t2' = is_indep (b,l,FindCompos.init_elem,collect_bargs,collect_bargs_sc) t2 in
		let side_condition = 
		  Terms.make_and_list (List.map (fun l' ->
		    Terms.make_or_list (List.map2 Terms.make_diff l l')
		      ) (!collect_bargs_sc))
		in
	        (* add probability; returns true if small enough to eliminate collisions, false otherwise. *)
		if add_term_collisions (cur_array, true_facts, [], side_condition) t1' t2' b (Some l) [charac_type] then
		  Some (Terms.make_or_list (List.map (fun l' ->   
		    let t2'' = Terms.replace l' l t2 in
		      Terms.make_and (Terms.make_and_list (List.map2 Terms.make_equal l l')) (Terms.make_equal t1 t2'')
		      ) (!collect_bargs)))
		else
		  None
	      with Not_found -> 
		None
	    end
       | _ -> None
      end 
  | _, FunApp(f,l) ->
      Terms.find_some (dependency_collision_rec3 cur_array true_facts t1 t2) l
  | _ -> None

(* [dependency_collision cur_array dep_info simp_facts t1 t2] simplifies [t1 = t2]
using dependency analysis.
It returns
- [Some t'] when it simplified [t1 = t2] into [t'];
- [None] when it could not simplify [t1 = t2]. 
[cur_array] is the list of current replication indices at [t1 = t2].
[dep_info] is the local dependency information (for module DepAnal2).
[simp_facts] contains facts that are known to hold. *)

let try_two_directions f t1 t2 =
  match f t1 t2 t1 with
    None -> f t2 t1 t2
  | x -> x

let dependency_collision cur_array dep_info simp_facts t1 t2 = 
  let t1' = try_no_var_rec simp_facts t1 in
  let t2' = try_no_var_rec simp_facts t2 in
  let true_facts = true_facts_from_simp_facts simp_facts in
  match try_two_directions (dependency_collision_rec2 cur_array true_facts dep_info) t1' t2' with
    (Some _) as x -> x
  | None ->
      repl_index_list := [];
      match try_two_directions (dependency_collision_rec3 cur_array true_facts) t1' t2' with
	(Some _) as x -> x
      | None ->
	  try_two_directions (dependency_collision_rec1 cur_array true_facts) t1' t2'

(* Note on the elimination of collisions in find conditions:
   The find indices are replaced with fresh replication indices,
   so that we correctly take into account that
   the condition of find is executed for every value of the indices. *)

(* Simplify a term knowing some true facts *)

let simplify_term cur_array dep_info keep_tuple simp_facts t = 
  let t' = 
    if keep_tuple then 
      Terms.try_no_var simp_facts t 
    else
      t
  in
  let t'' = Facts.simplify_term (dependency_collision cur_array dep_info) simp_facts t' in
  if !Settings.minimal_simplifications then
    begin
      if Terms.is_true t'' || Terms.is_false t'' || (not (Terms.synt_equal_terms t' t'')) ||
         (keep_tuple && Terms.is_tuple t'' && not (Terms.is_tuple t)) then
	begin
	  if not (Terms.is_true t || Terms.is_false t) then 
	    begin
	      Settings.changed := true;
	      current_pass_transfos := (SReplaceTerm(t,t'')) :: (!current_pass_transfos)
	    end;
	  t''
	end
      else
	(* The change is not really useful, don't do it *)
	t
    end
  else
    begin
      if not (Terms.synt_equal_terms t t'') then 
	begin
	  Settings.changed := true;
	  current_pass_transfos := (SReplaceTerm(t,t'')) :: (!current_pass_transfos)
	end;
      t''
    end

(*
let simplify_term cur_array dep_info k s t =
  let res = simplify_term cur_array dep_info k s t in
  if not (Terms.synt_equal_terms t res) then
    begin
      print_string "Simplifying "; Display.display_term t;
      print_string " knowing\n";
      Facts.display_facts s; 
      print_string "Simplify done "; Display.display_term res;
      print_newline();
      print_newline()
    end;
  res
*)

(* Simplify pattern *)

let rec simplify_pat cur_array dep_info true_facts = function
    (PatVar b) as pat -> pat
  | PatTuple (f,l) -> PatTuple (f,List.map (simplify_pat cur_array dep_info true_facts) l)
  | PatEqual t -> PatEqual (simplify_term cur_array dep_info false true_facts t)


(* Try to determine when a defined condition is always false
   b = variable
   pp = program point, at which we test whether b is defined
   lcp = length of the longest common prefix between the current replication
   indexes at pp and the indexes of b
   cur_array = current replication indexes at pp

   check_compatible ... p returns a pair (has_b,has_pp) where
   has_b is true when b is defined in p
   has_pp is true when pp is a branch in a subprocess of p
   It raises exception Compatible when b may be defined at pp
 *)

module CompatibleDefs
=
struct

type program_point =
    Term of term
  | Process of process

exception Compatible

let rec check_compatiblefc b pp def_node_opt t' =
  let has_pp0 = 
    match pp with
      Term t'' -> t' == t''
    | Process _ -> false
  in
  match t'.t_desc with
  | ResE(b',t) ->
      let (has_b, has_pp) = check_compatiblefc b pp def_node_opt t in
      if (b' == b) && has_pp then
	raise Compatible;
      (has_b || (b' == b), has_pp || has_pp0)
  | TestE(_, p1, p2) -> 
      let (has_b1, has_pp1) = check_compatiblefc b pp def_node_opt p1 in
      let (has_b2, has_pp2) = check_compatiblefc b pp def_node_opt p2 in
      (has_b1 || has_b2, has_pp1 || has_pp2 || has_pp0)
  | FindE(l0, p2, _) ->
      let (has_b2, has_pp2) = check_compatiblefc b pp def_node_opt p2 in
      let rec check_l = function
	  [] -> (false, false)
	| ((bl,def_list,t,p1)::l) ->
	    let (has_br, has_ppr) = check_l l in
	    let (_, has_ppt) = check_compatiblefc b pp def_node_opt t in
	    let (has_b1, has_pp1) = check_compatiblefc b pp def_node_opt p1 in
	    let has_b0 = List.exists (fun (b', _) -> b' == b) bl in
	    if has_b0 && has_pp1 then
	      raise Compatible;
	    (has_br || has_b1 || has_b0, has_ppr || has_ppt || has_pp1)
      in
      let (has_bl, has_ppl) = check_l l0 in
      (has_bl || has_b2, has_ppl || has_pp2 || has_pp0)
  | LetE(pat, _, p1, topt) ->
      let (has_b1, has_pp1) = check_compatiblefc b pp def_node_opt p1 in
      let (has_b2, has_pp2) = 
	match topt with
	  None -> (false, false)
	| Some p2 -> check_compatiblefc b pp def_node_opt p2 
      in
      let has_b3 = Terms.occurs_in_pat b pat in
      if has_b3 && has_pp1 then 
	raise Compatible;
      (has_b1 || has_b2 || has_b3, has_pp1 || has_pp2 || has_pp0)
  | Var _ | FunApp _ | ReplIndex _ -> (false, has_pp0) (* Will not contain any find/test or variable definition *)
  | EventAbortE _ -> Parsing_helper.internal_error "Event should have been expanded"

let rec check_compatible lcp b pp def_node_opt p' = 
  match p'.i_desc with
    Nil -> (false, false)
  | Par(p1,p2) ->
      let (has_b1, has_pp1) = check_compatible lcp b pp def_node_opt p1 in
      let (has_b2, has_pp2) = check_compatible lcp b pp def_node_opt p2 in
      if (has_b1 && has_pp2) || (has_b2 && has_pp1) then
	raise Compatible;
      (has_b1 || has_b2, has_pp1 || has_pp2)
  | Repl(b',p) ->
      if lcp <= 0 then
	(* When lcp <= 0, we have Compatible as soon as b is defined in p and pp occurs in p,
           and this can be tested very efficiently using definition nodes *)
	let (has_b, has_pp) =
	  match def_node_opt with
	    None -> check_compatible (lcp-1) b pp def_node_opt p
	  | Some (_,_,pp_node) ->
	      (* Returns true when p' is above node n *)
	      let rec find p' n =
		match n.definition with
		  DInputProcess p'' when p'' == p' -> true
		| _ -> if n.above_node == n then false else find p' n.above_node
	      in
	      (List.exists (find p') b.def, find p' pp_node)
	in
	if has_b && has_pp then
	  raise Compatible;
	(has_b, has_pp)
      else
	check_compatible (lcp-1) b pp def_node_opt p 
  | Input(_,pat, p) ->
      let (has_b, has_pp) = check_compatibleo lcp b pp def_node_opt p in
      let has_b2 = Terms.occurs_in_pat b pat in
      if has_b2 && has_pp then
	raise Compatible;
      (has_b || has_b2, has_pp)

and check_compatibleo lcp b pp def_node_opt p =
  let has_pp0 =
    match pp with
      Process p' -> p == p'
    | Term _ -> false
  in
  match p.p_desc with
    Yield | EventAbort _ -> (false, has_pp0)
  | Restr(b',p) ->
      let (has_b, has_pp) = check_compatibleo lcp b pp def_node_opt p in
      if (b' == b) && has_pp then
	raise Compatible;
      (has_b || (b' == b), has_pp || has_pp0)
  | Test(_, p1, p2) -> 
      let (has_b1, has_pp1) = check_compatibleo lcp b pp def_node_opt p1 in
      let (has_b2, has_pp2) = check_compatibleo lcp b pp def_node_opt p2 in
      (has_b1 || has_b2, has_pp1 || has_pp2 || has_pp0)
  | Find(l0, p2, _) ->
      let (has_b2, has_pp2) = check_compatibleo lcp b pp def_node_opt p2 in
      let rec check_l = function
	  [] -> (false, false)
	| ((bl,def_list,t,p1)::l) ->
	    let (has_br, has_ppr) = check_l l in
	    let (_, has_ppt) = check_compatiblefc b pp def_node_opt t in
	    let (has_b1, has_pp1) = check_compatibleo lcp b pp def_node_opt p1 in
	    let has_b0 = List.exists (fun (b',_) -> b' == b) bl in
	    if has_b0 && has_pp1 then
	      raise Compatible;
	    (has_br || has_b1 || has_b0, has_ppr || has_ppt || has_pp1)
      in
      let (has_bl, has_ppl) = check_l l0 in
      (has_bl || has_b2, has_ppl || has_pp2 || has_pp0)
  | Let(pat, _, p1, p2) ->
      let (has_b1, has_pp1) = check_compatibleo lcp b pp def_node_opt p1 in
      let (has_b2, has_pp2) = check_compatibleo lcp b pp def_node_opt p2 in
      let has_b3 = Terms.occurs_in_pat b pat in
      if has_b3 && has_pp1 then 
	raise Compatible;
      (has_b1 || has_b2 || has_b3, has_pp1 || has_pp2 || has_pp0)
  | Output(_,_,p) ->
      let (has_b, has_pp) = check_compatible lcp b pp def_node_opt p in
      (has_b, has_pp || has_pp0)
  | EventP(_,p) ->
      let (has_b, has_pp) = check_compatibleo lcp b pp def_node_opt p in
      (has_b, has_pp || has_pp0)
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"


let check_compatible_main b args pp cur_array simp_facts def_node_opt =
  let rec get_lcp l1 l2 = 
    match (l1,l2) with
      ({ t_desc = ReplIndex(b1) }::l1',b2::l2') when b1 == b2 ->
	1 + get_lcp l1' l2' 
    | (t::l1',b2::l2') ->
	begin
	  match Terms.try_no_var simp_facts t with
	    { t_desc = ReplIndex(b1) } when b1 == b2 ->
	      1 + get_lcp l1' l2' 
	  | _ -> 0
	end
    | _ -> 0
  in
  let lcp = get_lcp (List.rev args) (List.rev cur_array) in
  try
    let (has_b, has_pp) = check_compatible lcp b pp def_node_opt (!whole_game).proc in
    if not has_pp then
      begin
	begin
	  match pp with
	    Term t -> print_string "Term "; Display.display_term t
	  | Process p -> print_string "Process "; Display.display_oprocess "" p
	end;
	Parsing_helper.internal_error "Program point not found in check_compatible_deflist"
      end;
    false
  with Compatible ->
    true


let rec check_compatible_deflist pp cur_array simp_facts def_node_opt def_list =
  List.for_all (fun (b,l) -> check_compatible_main b l pp cur_array simp_facts def_node_opt) def_list

end


(* check_compatible2_deflist checks that all pairs of variables that must 
   be defined can be simultaneously defined.
   Uses the field "compatible" set by Terms.build_compatible_defs
 *)


module CompatibleDefs2
=
struct

let rec check_compatible2_main fact_accu = function
    [] -> ()
  | (a::l) -> 
      List.iter (Terms.both_def_add_fact fact_accu a) l;
      check_compatible2_main fact_accu l

let check_compatible2_deflist old_def_list def_list =
  (* Remove the already defined variables from the new def_list *)
  let new_def_list = List.filter (fun br -> not (Terms.mem_binderref br old_def_list)) def_list in
  (* Check that the newly defined variables are compatible with each other *)
  let fact_accu = ref [] in 
  check_compatible2_main fact_accu new_def_list; 
  (* ... and with all the previously defined variables *)
  List.iter (fun br -> List.iter (Terms.both_def_add_fact fact_accu br) new_def_list) old_def_list;
  !fact_accu

end

(* If a find condition is not a basic term (without if/let/find/new),
   I should not apply it to a function, because it breaks the 
   invariant that if/let/find/new are at the root of find conditions.

   Another option would be to expand the obtained term by
   Transform.final_pseudo_expand.
 *)

exception CannotExpand

let make_and_find_cond t t' =
  match t.t_desc, t'.t_desc with
    (Var _ | FunApp _), (Var _ | FunApp _) -> Terms.make_and t t'
  | _ -> raise CannotExpand


let needed_vars vars = List.exists Terms.has_array_ref_q vars

let needed_vars_in_pat pat =
  needed_vars (Terms.vars_from_pat [] pat)

(* [has_array_access b t] returns true when [b] has an array reference
   in [t] with indexes different from the indexes at creation *)

let rec has_array_access b t =
  match t.t_desc with
    Var(b',l) -> 
      ((b == b') && not (Terms.is_args_at_creation b l)) ||
      (List.exists (has_array_access b) l)
  | ReplIndex _ -> false
  | FunApp(f,l) ->
      List.exists (has_array_access b) l
  | ResE(b',t) -> has_array_access b t
  | TestE(t1,t2,t3) -> 
      (has_array_access b t1) || (has_array_access b t2) || (has_array_access b t3)
  | FindE(l0,t3,_) ->
      (List.exists (fun (bl,def_list,t1,t2) ->
	(List.exists (has_array_access_br b) def_list) ||
	(has_array_access b t1) || (has_array_access b t2)
	) l0) || (has_array_access b t3)
  | LetE(pat,t1,t2,topt) ->
      (has_array_access_pat b pat) ||
      (has_array_access b t1) || 
      (has_array_access b t2) || 
      (match topt with
	None -> false
      |	Some t3 -> has_array_access b t3)
  | EventAbortE _ ->
     Parsing_helper.internal_error "Event should have been expanded"

and has_array_access_br b (b',l) =
  ((b == b') && not (Terms.is_args_at_creation b l)) ||
  (List.exists (has_array_access b) l)

and has_array_access_pat b = function
    PatVar _ -> false
  | PatTuple(_,l) -> List.exists (has_array_access_pat b) l
  | PatEqual t -> has_array_access b t

(* Collect array accesses to variables in [bl] that occur in [def_list].
   Store them in [accu]. *)

let rec collect_array_accesses_br accu bl (b,l) =
  if (List.memq b bl) && (not (Terms.is_args_at_creation b l)) then
    Terms.add_binderref (b,l) accu;
  List.iter (collect_array_accesses_t accu bl) l

and collect_array_accesses_t accu bl t =
  match t.t_desc with
    Var(b,l) -> collect_array_accesses_br accu bl (b,l)
  | ReplIndex _ -> ()
  | FunApp(f,l) -> List.iter (collect_array_accesses_t accu bl) l
  | _ -> Parsing_helper.internal_error "If/let/find/new should not occur in def_list"

let collect_array_accesses accu bl def_list =
  List.iter (collect_array_accesses_br accu bl) def_list

(* size of an array access *)

let rec size t =
  match t.t_desc with
    ReplIndex _ -> 1
  | Var(_,l) | FunApp(_,l) -> 1 + size_list l
  | _ -> Parsing_helper.internal_error "If/let/find/new should not occur in def_list"

and size_list = function
    [] -> 0
  | (a::l) -> size a + size_list l

let rec size_br (b,l) = size_list l

(* sort list in increasing size order *)

let sort_fun br1 br2 = size_br br1 - size_br br2

(* Helper functions for expanding find in find branch 

   make_and_find_cond requires that the find condition is a basic term
   Var/FunApp, so I do not need to rewrite that term to update args_at_creation
   of variables defined inside it. (There are no such variables.) *)

let rec generate_branches_rec ((bl, _, _, _) as ext_branch) (bl3, def_list3, t3, p4) = function
    [] -> (* no array accesses to variables in bl in def_list3 *)
      (* Replace references to variables in bl with the corresponding 
	 replication indices in def_list3/t3 (because def_list3/t3 occurred 
	 in the "then" branch before transformation, and occur in the 
	 condition after transformation). *)
      let bl_rev_subst = List.map (fun (b,b') -> (b, Terms.term_from_repl_index b')) bl in
      let def_list3' = Terms.subst_def_list3 bl_rev_subst def_list3 in
      let t3' = Terms.subst3 bl_rev_subst t3 in
      [(bl3, def_list3', t3', p4)]
  | ((b, l) as br)::rest ->
      let branches_rest = generate_branches_rec ext_branch (bl3, def_list3, t3, p4) rest in
      (* Case the array access to br is in fact done with the current replication
	 indices => I replace br with the corresponding replication index *)
      let subst = Terms.OneSubstArgs(br, Terms.term_from_repl_index (List.assq b bl)) in
      (List.map (fun (bl', def_list', t', p') -> 
	(bl', Terms.copy_def_list subst def_list', 
	 make_and_find_cond (Terms.copy_term subst t') 
	   (Terms.make_and_list (List.map2 (fun t ri -> Terms.make_equal t (Terms.term_from_repl_index ri)) l b.args_at_creation)), p')) branches_rest)
      (* Case the array access to br is done with indices different from the current 
	 replication indices => I can leave br as it is *)
      @ branches_rest

let generate_branches ((bl, def_list, t, _) as ext_branch) ((bl3, def_list3, t3, p4) as br) =
  let accu = ref [] in
  collect_array_accesses accu (List.map fst bl) def_list3;
  (* In case of nested array references, I need to handle the bigger
     array reference first (so it must occur last in the list),
     because after substitution of the smaller one with an index variable,
     we would not recognize the bigger one. 
     To do that, I sort the list of array accesses by increasing size. *)
  let array_accesses_sorted = List.sort sort_fun (!accu) in
  let br' = generate_branches_rec ext_branch br array_accesses_sorted in
  List.map (fun (bl3, def_list3, t3, p4) ->
    (bl @ bl3, def_list @ def_list3, make_and_find_cond t t3, p4)) br'

(* Add lets *)

let rec add_let p = function
    [] -> p
  | ((b, b_im)::l) ->
      Terms.oproc_from_desc (Let(PatVar b, b_im, add_let p l, Terms.oproc_from_desc Yield))

let rec add_let_term p = function
    [] -> p
  | ((b, b_im)::l) ->
      Terms.build_term_type p.t_type (LetE(PatVar b, b_im, add_let_term p l, None))

(* [is_unique l0' find_info] returns Unique when a [find] is unique,
   that is, at runtime, there is always a single possible branch 
   and a single possible value of the indices:
   either it is marked [Unique] in the [find_info],
   or it has a single branch with no index.
   [l0'] contains the branches of the considered [find]. *)

let is_unique l0' find_info =
  match l0' with
    [([],_,_,_)] -> Unique
  | _ -> find_info

(* Simplification of terms with if/let/find/res.
   The simplifications are very similar to those performed
   on processes below. *)

exception OneBranchTerm of term findbranch

let rec simplify_term_w_find cur_array true_facts t =
  simplify_term_w_find_modified cur_array true_facts t t

(* [simplify_term_w_find_modified] is useful in case the term is modified 
   with respect to the term inside the process in (!whole_game), 
   before being passed to the simplification function. 
   The term t_orig is the term before modification.
   We use t_orig as a marker for the current program point
   (in CompatibleDefs.check_compatible_deflist). *)
and simplify_term_w_find_modified cur_array true_facts t_orig t =
  match t.t_desc with
    Var _ | FunApp _ | ReplIndex _ ->     
      simplify_term cur_array DepAnal2.init false true_facts t
  | TestE(t1,t2,t3) ->
      begin
      let t1' = simplify_term cur_array DepAnal2.init false true_facts t1 in
      let t_or_and = Terms.or_and_form t1' in
      try
	(* The facts that are true in the "else" branch *)
	let true_facts' = Facts.simplif_add (dependency_collision cur_array DepAnal2.init) true_facts (Terms.make_not t1') in
	(* Check that the variables known to be defined are 
           compatible. This check is useful when the condition
           (not t1') shows that some index terms are equal to
	   the current replication indices. *)
	let def_vars_accu = Facts.get_def_vars_at t.t_facts in
	if not (CompatibleDefs.check_compatible_deflist (CompatibleDefs.Term t_orig) cur_array true_facts' t.t_facts def_vars_accu) then
	  raise Contradiction;
	(* Simplify the "else" branch *)
	let t3' = simplify_term_w_find cur_array true_facts' t3 in
	simplify_term_if t_orig t cur_array true_facts t2 t3' t_or_and
      with Contradiction ->
	Settings.changed := true;
	current_pass_transfos := (STestETrue(t)) :: (!current_pass_transfos);
	simplify_term_w_find cur_array true_facts t2
      end

  | FindE(l0,t3,find_info) -> 
      begin
      (* Expand find in conditions of find when the inner find is "unique".
	 The outer find is unique after transformation if and only if it
	 was unique before transformation. *)
      let done_expand = ref false in
      let l0' = 
	if (!Settings.unique_branch_reorg) then
	  try
	  let rec expand_find = function
	      [] -> []
	    | (((bl, def_list, t', t2) as br1)::r) ->
		let r' = expand_find r in 
		match t'.t_desc with
		  FindE(l2, t4, find_info') when Terms.is_false t4 && (is_unique l2 find_info' == Unique) ->
		    let result = 
		      (List.map (fun (bl3, def_list3, t5, t6) ->
			(* Replace references to variables in bl3 with the corresponding 
			   replication indices in t6 (because t6 occurred in the "then" branch
			   before transformation, and occurs in the condition after
			   transformation). 
			   The transformation would be incorrect if t6 tested for the definition
			   of variables in bl3, because these variables are defined more
			   in the initial game than in the transformed game.
			   However, this cannot happen because variables of bl3 are defined
			   in the condition of a find, so there are no array accesses on them. *)
			let t6' = Terms.subst3 (List.map (fun (b,b') -> (b, Terms.term_from_repl_index b')) bl3) t6 in
			(* The variables in bl3 are no longer used, but I need to have some variables there.
			   Moreover, the old variables of bl3 cannot be kept, because their
			   args_at_creation is not correct in the transformed game *)
			let bl3' = List.map (fun (b,b') -> (Terms.create_binder b.sname (Terms.new_vname()) b.btype cur_array, b')) bl3 in
			(bl @ bl3', def_list @ def_list3, make_and_find_cond t5 t6', t2)) l2) @ r'
		    in
		    done_expand := true;
		    current_pass_transfos := (SFindinFindECondition(t,t')) :: (!current_pass_transfos);
		    result
		| _ -> br1 :: r'
	  in
	  expand_find l0
	  with CannotExpand -> l0
	else
	  l0
      in
      if (!done_expand) then
	begin
	  Settings.changed := true;
	  let find_info = is_unique l0' find_info in
	  Terms.build_term2 t (FindE(l0', t3, find_info))
	end
      else

      (* Expand find in branch of find when both finds are "unique"
	 TO DO I could perform several of these transformations in a single step,
	 but I'm not sure if I want to have many nested Finds in the else branch *)
      let l0', t3' = 
	if (!Settings.unique_branch_reorg) then
	  try
	  let rec expand_find seen = function
	      [] -> l0, t3
	    | (((bl, def_list, t', t2) as br1)::r) ->
		match t2.t_desc with
		  FindE(l3, t4, Unique) when (find_info == Unique) -> 
		    (* bl is defined in a condition of find, so these variables
		       will be SArenamed by auto_sa_rename. This SArename advice is
		       therefore not necessary. 
		    List.iter (fun b ->
		      Settings.advise := Terms.add_eq (SArenaming b) (!Settings.advise)) bl;
		    *)

		    let result = 
		      (List.rev_append seen ((List.concat (List.map (generate_branches br1) l3)) @ r)),
		      (Terms.build_term_type t3.t_type (FindE([bl, def_list, t', t4], t3, Unique)))
		    in
		    current_pass_transfos := (SFindinFindEBranch(t,t2)) :: (!current_pass_transfos);
		    result
		| _ -> expand_find (br1::seen) r
	  in
	  expand_find [] l0
	  with CannotExpand -> l0,t3
	else
	  l0, t3
      in
      if l0' != l0 then
	begin
	  Settings.changed := true;
	  let find_info = is_unique l0' find_info in
	  Terms.build_term2 t (FindE(l0', t3', find_info))
	end
      else

      match l0 with
	[] ->
	  simplify_term_w_find cur_array true_facts t3
      |	[([],def_list,t1,t2)] when Facts.reduced_def_list t.t_facts def_list = [] && 
	                              (match t1.t_desc with Var _ | FunApp _ -> true | _ -> false) -> 
	  Settings.changed := true;
	  current_pass_transfos := (SFindEtoTestE t) :: (!current_pass_transfos);
	  simplify_term_w_find_modified cur_array true_facts t_orig (Terms.build_term2 t (TestE(t1,t2,t3)))
      |	_ -> 
      let def_vars = Facts.get_def_vars_at t.t_facts in
      let t3' = 
	try
	  simplify_term_w_find cur_array (add_elsefind (dependency_collision cur_array DepAnal2.init) def_vars true_facts l0) t3
	with Contradiction ->
	  (* The else branch of the find will never be executed
             => use some constant to simplify *)
	  match t3.t_desc with
	    FunApp(_,[]) -> t3 (* t3 is already a constant, leave it as it is *)
	  | _ ->
	      Settings.changed := true;
	      current_pass_transfos := (SFindEElseRemoved(t)) :: (!current_pass_transfos);
	      Terms.cst_for_type t3.t_type
      in
      let rec simplify_findl = function
	  [] -> []
	| (bl, def_list, t1, t2)::l ->
	    begin
	    let l' = simplify_findl l in
	    let vars = List.map fst bl in
	    let repl_indices = List.map snd bl in
	    let cur_array_cond = repl_indices @ cur_array in
	    let vars_terms = List.map Terms.term_from_binder vars in
	    try
	      let this_branch_node = Facts.get_node t.t_facts in 
	      let def_list' = Facts.reduced_def_list t.t_facts def_list in
	      let def_vars_cond = Facts.def_vars_from_defined this_branch_node def_list' in
	      let true_facts = filter_elsefind (Terms.not_deflist_l vars) true_facts in
	      let facts_def_list = Facts.facts_from_defined this_branch_node def_list in
	      let true_facts_t1 = Facts.simplif_add_list (dependency_collision cur_array_cond DepAnal2.init) true_facts facts_def_list in
	      let facts_from_elsefind_facts =
		if !Settings.elsefind_facts_in_simplify then
		  let def_vars_cond' = Terms.union_binderref def_vars_cond def_vars in
		  Simplify1.get_facts_of_elsefind_facts (!whole_game) cur_array_cond true_facts_t1 def_vars_cond'
		else
		  []
	      in
	      let true_facts_t1 = Facts.simplif_add_list (dependency_collision cur_array_cond DepAnal2.init) true_facts_t1 facts_from_elsefind_facts in
	      (* Set priorities of variables defined by this find, 
	         to orient rewrite rules preferably in the direction
	         b[..] -> t where b \in bl *)
	      incr current_max_priority;
	      List.iter (fun b -> 
		b.priority <- (!current_max_priority); 
		priority_list := b :: (!priority_list)) vars;
	      let (t1', facts_cond) =
		match t1.t_desc with
		  Var _ | FunApp _ ->
		    let t1' = simplify_term cur_array_cond DepAnal2.init false true_facts_t1 t1 in
		    (t1', t1' :: facts_from_elsefind_facts @ facts_def_list)
		| _ -> 
		    let t1' = simplify_term_w_find cur_array_cond true_facts_t1 t1 in
		    (t1', facts_from_elsefind_facts @ facts_def_list)
	      in

	      (* [facts_cond] contains the facts that hold,
		 using repl_indices as indices. We substitute vars from them to obtain
		 the facts that hold in the then branch.*)
	      let facts_cond' = List.map (Terms.subst repl_indices vars_terms) facts_cond in
	      let tf' = Facts.simplif_add_list (dependency_collision cur_array DepAnal2.init) true_facts facts_cond' in

	      (* Check that the "defined" conditions can hold,
		 if not remove the branch *)
	      (* [def_vars_cond] contains the variables that are certainly defined 
		 using repl_indices as indices. We substitute vars from them to obtain
		 the variables certainly defined in the then branch. *)
	      let def_vars_accu = Terms.subst_def_list repl_indices vars_terms def_vars_cond in
	      (* check_compatible_deflist checks that the variables in def_vars_accu can be defined
	         at the current program point *)
	      if not (CompatibleDefs.check_compatible_deflist (CompatibleDefs.Term t_orig) cur_array tf' t.t_facts def_vars_accu) then
		raise Contradiction;
	      (* check_compatible2_deflist checks that all pairs of variables 
		 that must be defined can be simultaneously defined. 
		 Useful in some examples, but costly! *)
	      let tf' = 
		if !Settings.detect_incompatible_defined_cond then
		  let new_facts = CompatibleDefs2.check_compatible2_deflist def_vars def_vars_accu in
		  Facts.simplif_add_list (dependency_collision cur_array DepAnal2.init) tf' new_facts 
		else tf'
	      in
	      let def_vars' = 
		(* Using def_vars_accu instead of def_list' is more precise *)
	        def_vars_accu @ def_vars
	      in
	      let tf' = convert_elsefind (dependency_collision cur_array DepAnal2.init) def_vars' tf' in
	      let t2' = simplify_term_w_find cur_array tf' t2 in

	      (* TO DO instead of taking the intersection with accu_def_list_subterm,
		 I should rather remove the variable references that are already 
		 guaranteed to be defined. (named [defined_refs] in invariants.ml,
		 for instance) However, I would need to compute those here. *)
	      let accu_def_list = ref def_list' in 
	      List.iter (Terms.get_deflist_subterms accu_def_list) facts_def_list;
	      let accu_def_list_subterm = ref [] in
	      List.iter (Terms.close_def_subterm accu_def_list_subterm) (!accu_def_list);
	      let accu_needed = ref [] in
	      Terms.get_deflist_subterms accu_needed t1';
	      (* Replace vars with repl_indices in t2', to get the variable
		 references that need to occur in the new def_list *)
	      let bl_rev_subst = List.map (fun (b,b') -> (b, Terms.term_from_repl_index b')) bl in
	      let t2'_repl_indices = Terms.subst3 bl_rev_subst t2' in
	      Terms.get_deflist_subterms accu_needed t2'_repl_indices; 
	      let accu_needed_subterm = ref [] in
	      List.iter (Terms.close_def_subterm accu_needed_subterm) (!accu_needed);
	      let needed_occur = 
		(Facts.reduced_def_list t.t_facts 
		   (Terms.inter_binderref (!accu_needed_subterm) (!accu_def_list_subterm))) in
	      let implied_needed_occur = Facts.def_vars_from_defined None needed_occur in
	      let def_list'' = Terms.setminus_binderref def_list' implied_needed_occur in
	      let def_list3 = Facts.remove_subterms [] (needed_occur @ (Facts.filter_def_list [] def_list'')) in

	      if List.length def_list3 < List.length def_list then
		begin
		  Settings.changed := true;
		  current_pass_transfos := (SFindEDeflist(t, def_list, def_list3)) :: (!current_pass_transfos)
		end
	      else if not (Facts.eq_deflists def_list def_list3)  then
		current_pass_transfos := (SFindEDeflist(t, def_list, def_list3)) :: (!current_pass_transfos);

	      (* When i = M implied by def_list & t, remove i from bl
		 and substitute M for i *)
	      let keep_bl = ref [] in
	      let subst = ref [] in
	      List.iter (fun (b, b') -> 
		let b_im = Terms.try_no_var tf' (Terms.term_from_binder b) in
		if (List.exists (fun (b', b_im') -> Terms.refers_to b b_im' || Terms.refers_to b' b_im) (!subst)) ||
		   (Terms.refers_to b b_im)
		then
		  keep_bl := (b, b') :: (!keep_bl)
		else
		  subst := (b, b_im) :: (!subst);
					  ) bl;
	      let bl' = !keep_bl in
	      if (!subst) != [] then
		begin
		  Settings.changed := true;
		  current_pass_transfos := (SFindEIndexKnown(t, (bl, def_list, t1, t2), !subst)) :: (!current_pass_transfos)
		end;
	      let subst_repl_indices_source = List.map (fun (b,_) -> List.assq b bl) (!subst) in
	      let subst_repl_indices_target = 
		List.map (fun (_, b_im) -> Terms.subst3 bl_rev_subst b_im) (!subst) 
	      in
	      let def_list_tmp = ref [] in
	      List.iter (fun br ->
		Terms.get_deflist_subterms def_list_tmp 
		  (Terms.subst subst_repl_indices_source subst_repl_indices_target (Terms.term_from_binderref br))) def_list3;
	      let def_list3 = !def_list_tmp in 
	      let t1' = Terms.update_args_at_creation ((List.map snd bl') @ cur_array) 
		  (Terms.subst subst_repl_indices_source subst_repl_indices_target t1') in
	      let t2' = add_let_term (Terms.subst3 (!subst) t2') (!subst) in
	      (* End of "When i = M implied by def_list & t, remove i from bl
		 and substitute M for i"*)

              let find_branch = (bl', def_list3, t1', t2') in

              (* If the find is marked "unique", and we can prove that
	         the current branch succeeds, keep only that branch *)
              if (!Settings.unique_branch) &&
		(match t1'.t_desc with
		  Var _ | FunApp _ -> true
		| _ -> false)
	      then 
		try 
		  branch_succeeds find_branch (dependency_collision cur_array_cond DepAnal2.init) true_facts def_vars;
		  find_branch :: l'
		with SuccessBranch(subst, keep_bl) ->
		  if not (find_info == Unique) then find_branch :: l' else
		  begin
		    (* Subst is a substitution for replication indices,
		       compute the substitution for the corresponding variables *)
		    let subst_repl_indices_source = List.map (fun (_,b,_) -> b) subst in
		    let subst_repl_indices_target = List.map (fun (_,_,b_im) -> b_im) subst in
		    let subst = List.map (fun (b, _, b_im) -> 
		      (b, Terms.subst repl_indices vars_terms b_im)
			) subst 
		    in
		    if List.exists (fun (b, b_im) -> 
		      List.exists (fun (b', b_im') -> Terms.refers_to b b_im') subst
			) subst
		    then raise (OneBranchTerm(find_branch));
		    if subst != [] then 
		      begin
			Settings.changed := true;
			current_pass_transfos := (SFindEIndexKnown(t1', (bl, def_list, t1, t2), subst)) :: (!current_pass_transfos)
		      end;
		    let def_list_tmp = ref [] in
		    List.iter (fun br ->
		      Terms.get_deflist_subterms def_list_tmp 
			(Terms.subst subst_repl_indices_source subst_repl_indices_target (Terms.term_from_binderref br))) def_list3;
		    let def_list3 = !def_list_tmp in 
		    let t1' = Terms.update_args_at_creation ((List.map snd keep_bl) @ cur_array) 
			(Terms.subst subst_repl_indices_source subst_repl_indices_target t1') in
		    let t2' = add_let_term (Terms.subst3 subst t2') subst in
		    raise (OneBranchTerm(keep_bl, def_list3, t1', t2'))
		  end
	      else
		find_branch :: l'

	      (*let t_or_and = Terms.or_and_form t' in
	      simplify_find true_facts' l' bl def_list' t_or_and p1 *)
	    with Contradiction ->
	      Settings.changed := true;
	      current_pass_transfos := (SFindEBranchRemoved(t,(bl, def_list, t1, t2))) :: (!current_pass_transfos);
	      l'
	    end
      in
      try 
	let l0' = simplify_findl l0 in
	if l0' == [] then
	  begin
	    Settings.changed := true;
	    current_pass_transfos := (SFindERemoved(t)) :: (!current_pass_transfos);
	    t3'
	  end
	else
	  let find_info = is_unique l0' find_info in
	  Terms.build_term2 t (FindE(l0', t3',find_info))
      with OneBranchTerm(find_branch) ->
	match find_branch with
	  ([],[],_,t2) -> 
	    Settings.changed := true;
	    current_pass_transfos := (SFindESingleBranch(t,find_branch)) :: (!current_pass_transfos);
	    t2
	| _ ->
            (* The else branch of the find will never be executed
               => use some constant to simplify *)
	    let t3'' = 
	      match t3'.t_desc with
		FunApp(_,[]) -> t3'
	      |	_ -> Terms.cst_for_type t3'.t_type 
	    in
	    if List.length l0 > 1 then 
	      begin
		Settings.changed := true;
		current_pass_transfos := (SFindESingleBranch(t,find_branch)) :: (!current_pass_transfos)
	      end
	    else if not (Terms.equal_terms t3' t3'') then
	      begin
		Settings.changed := true;
		current_pass_transfos := (SFindEElseRemoved(t)) :: (!current_pass_transfos)
	      end;
	    Terms.build_term2 t (FindE([find_branch], t3'',find_info))
      end

  | LetE(pat,t1,t2,topt) ->
      begin
      let true_facts' = filter_elsefind (Terms.not_deflist_l (Terms.vars_from_pat [] pat)) true_facts in
      let t1' = simplify_term cur_array DepAnal2.init (Terms.is_pat_tuple pat) true_facts t1 in
      let true_facts_else =
	try
	  Facts.simplif_add (dependency_collision cur_array DepAnal2.init) true_facts (Terms.make_for_all_diff (Terms.gen_term_from_pat pat) t1)
	with Terms.NonLinearPattern | Contradiction 
          (* TO DO We ignore the contradiction here. A contradiction happens 
	     when the [let] always succeeds; we could modify the else branch 
	     to any term *) -> true_facts
      in
      simplify_term_let t_orig t true_facts_else cur_array true_facts' t2 topt t1' pat
      end

  | ResE(b,t0) ->
      let true_facts = filter_elsefind (Terms.not_deflist b) true_facts in
      let t' = simplify_term_w_find cur_array true_facts t0 in
      if not ((Terms.has_array_ref_q b) || (Terms.refers_to b t0)) then
	begin
	  Settings.changed := true;
	  current_pass_transfos := (SResERemoved(t)) :: (!current_pass_transfos);
	  t'
	end
      else if not (b.array_ref || b.std_ref || (Settings.occurs_in_queries b)) then
	begin
	  Settings.changed := true;
	  current_pass_transfos := (SResEToAssign(t)) :: (!current_pass_transfos);
	  Terms.build_term2 t (LetE(PatVar b,  Terms.cst_for_type b.btype, t', None))
	end
      else
	Terms.build_term2 t (ResE(b, t'))

  | EventAbortE _ ->
      Parsing_helper.internal_error "Event should have been expanded"

and simplify_term_if t_orig if_t cur_array true_facts ttrue tfalse t' =
  match t'.t_desc with
    FunApp(f, []) when f == Settings.c_false -> 
      Settings.changed := true;
      current_pass_transfos := (STestEFalse(if_t)) :: (!current_pass_transfos);
      tfalse
  | FunApp(f, []) when f == Settings.c_true -> 
      Settings.changed := true;
      current_pass_transfos := (STestETrue(if_t)) :: (!current_pass_transfos);
      simplify_term_w_find cur_array true_facts ttrue
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      Settings.changed := true;
      current_pass_transfos := (STestEOr(if_t)) :: (!current_pass_transfos);
      simplify_term_if t_orig if_t cur_array true_facts ttrue (simplify_term_if t_orig if_t cur_array true_facts ttrue tfalse t2) t1
  | _ -> 
      try
	let true_facts' = Facts.simplif_add (dependency_collision cur_array DepAnal2.init) true_facts t' in
	(* Check that the variables known to be defined are 
           compatible. This check is useful when the condition
           of "if" shows that some index terms are equal to
	   the current replication indices. *)
	let def_vars_accu = Facts.get_def_vars_at if_t.t_facts in
	if not (CompatibleDefs.check_compatible_deflist (CompatibleDefs.Term t_orig) cur_array true_facts' if_t.t_facts def_vars_accu) then
	  raise Contradiction;
	(* Simplify the "then" branch *)
	let ttrue' = simplify_term_w_find cur_array true_facts' ttrue in
	Terms.build_term2 if_t (TestE(t', ttrue', tfalse))
      with Contradiction ->
	Settings.changed := true;
	current_pass_transfos := (STestEFalse(if_t)) :: (!current_pass_transfos);
	tfalse

and simplify_term_let t_orig let_t true_facts_else cur_array true_facts ttrue tfalse t' = function
    (PatVar b) as pat -> 
      if tfalse != None then 
	begin
	  Settings.changed := true;
	  current_pass_transfos := (SLetEElseRemoved(let_t)) :: (!current_pass_transfos);
	end;
      Terms.build_term2 let_t (LetE(pat, t', simplify_term_w_find cur_array (Facts.simplif_add (dependency_collision cur_array DepAnal2.init) true_facts (Terms.make_let_equal 
	(Terms.term_from_binder b) t')) ttrue, None))
  | (PatEqual t) as pat ->
      Settings.changed := true;
      current_pass_transfos := (SLetESimplifyPattern(let_t, pat, DEqTest)) :: (!current_pass_transfos);
      begin
	match tfalse with
	  None -> Parsing_helper.internal_error "missing else branch of let"
	| Some t3 ->
	    simplify_term_w_find_modified cur_array true_facts t_orig (Terms.build_term2 let_t (TestE(Terms.make_equal t t', ttrue, t3)))
      end
  | (PatTuple (f,l)) as pat ->
      begin
	match tfalse with
	  None -> Parsing_helper.internal_error "missing else branch of let"
	| Some t3 ->
	try 
	  let res = simplify_term_w_find_modified cur_array true_facts t_orig
	      (Terms.put_lets_term l (Terms.split_term f t') ttrue tfalse)
	  in
	  Settings.changed := true;
	  current_pass_transfos := (SLetESimplifyPattern(let_t, pat, DExpandTuple)) :: (!current_pass_transfos);
	  res
	with 
	  Not_found -> 
	    begin
	      try
		let ttrue' = simplify_term_w_find cur_array (Facts.simplif_add (dependency_collision cur_array DepAnal2.init) true_facts 
		   (Terms.make_equal (Terms.term_from_pat pat) t')) ttrue
		in
		Terms.build_term2 let_t (LetE(pat, t', ttrue', Some (simplify_term_w_find cur_array true_facts_else t3)))
	      with Contradiction ->
		Settings.changed := true;
		current_pass_transfos := (SLetERemoved(let_t)) :: (!current_pass_transfos);
		simplify_term_w_find cur_array true_facts_else t3
	    end
	| Terms.Impossible -> 
	    Settings.changed := true;
	    current_pass_transfos := (SLetESimplifyPattern(let_t, pat, DImpossibleTuple)) :: (!current_pass_transfos);
	    simplify_term_w_find cur_array true_facts_else t3
      end


(* Simplification of processes *)

exception OneBranchProcess of process findbranch

let rec simplify_process cur_array dep_info true_facts p = 
  let dep_info' = DepAnal2.update_dep_info cur_array dep_info true_facts p in
  Terms.iproc_from_desc2 p (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) -> Par(simplify_process cur_array dep_info' true_facts p1,
		      simplify_process cur_array dep_info' true_facts p2)
  | Repl(b,p) -> Repl(b, simplify_process (b::cur_array) dep_info' true_facts p)
  | Input((c,tl), pat, p) ->
      begin
	match true_facts with
	  (_,_,[]) -> ()
	| _ -> Parsing_helper.internal_error "There should be no elsefind facts at inputs"
      end;
      Input((c, List.map (fun t -> simplify_term cur_array dep_info false true_facts t) tl), 
	    simplify_pat cur_array dep_info true_facts pat, 
	    simplify_oprocess cur_array dep_info' true_facts p))


and simplify_oprocess cur_array dep_info true_facts p =
  simplify_oprocess_modified cur_array dep_info true_facts p p

(* [simplify_oprocess_modified] is useful in case the process is modified 
   with respect to the process in (!whole_game), before being passed to
   the simplification function. 
   The process p_orig is the process before modification.
   We use p_orig as a marker for the current program point
   (in CompatibleDefs.check_compatible_deflist). *)
and simplify_oprocess_modified cur_array dep_info true_facts p_orig p =
  let (p', dep_info_list') = DepAnal2.update_dep_infoo cur_array dep_info true_facts p in
  match p'.p_desc with
    Yield -> Terms.oproc_from_desc Yield
  | EventAbort f -> Terms.oproc_from_desc2 p' (EventAbort f)
  | Restr(b,p0) -> 
      let true_facts = filter_elsefind (Terms.not_deflist b) true_facts in
      let p1 = simplify_oprocess cur_array (List.hd dep_info_list') true_facts p0 in
      if not ((Terms.has_array_ref_q b) || (Terms.refers_to_oprocess b p0)) then
	begin
	  Settings.changed := true;
	  current_pass_transfos := (SResRemoved(p')) :: (!current_pass_transfos);
	  p1
	end
      else if not (b.array_ref || b.std_ref || (Settings.occurs_in_queries b)) then
	begin
	  Settings.changed := true;
	  current_pass_transfos := (SResToAssign(p')) :: (!current_pass_transfos);
	  Terms.oproc_from_desc2 p' (Let(PatVar b,  Terms.cst_for_type b.btype, p1, Terms.oproc_from_desc Yield))
	end
      else
	Terms.oproc_from_desc2 p' (Restr(b, p1))
  | Test(t, p1, p2) ->
      begin
      let dep_info_branch = List.hd dep_info_list' in
      let t' = simplify_term cur_array dep_info false true_facts t in
      let t_or_and = Terms.or_and_form t' in
      try
	(* The facts that are true in the "else" branch *)
	let true_facts' = Facts.simplif_add (dependency_collision cur_array dep_info) true_facts (Terms.make_not t') in
	(* Check that the variables known to be defined are 
           compatible. This check is useful when the condition
           (not t1') shows that some index terms are equal to
	   the current replication indices. *)
	let def_vars_accu = Facts.get_def_vars_at p'.p_facts in
	if not (CompatibleDefs.check_compatible_deflist (CompatibleDefs.Process p_orig) cur_array true_facts' p'.p_facts def_vars_accu) then
	  raise Contradiction;
	(* Simplify the "else" branch *)
	let p2' = simplify_oprocess cur_array dep_info_branch true_facts' p2 in
	simplify_if p_orig p' dep_info_branch cur_array true_facts p1 p2' t_or_and
      with Contradiction ->
	Settings.changed := true;
	current_pass_transfos := (STestTrue(p')) :: (!current_pass_transfos);	  	
	simplify_oprocess cur_array dep_info_branch true_facts p1
      end
  | Find(l0, p2, find_info) ->
      begin
      match dep_info_list' with
	[] -> Parsing_helper.internal_error "Non empty dep_info_list' needed"
      |	dep_info_else :: dep_info_branches ->

      (* Expand find in conditions of find when the inner find is "unique"
	 The outer find is unique after transformation iff it is unique before transformation *)
      let done_expand = ref false in
      let l0' = 
	if (!Settings.unique_branch_reorg) then
	  try
	  let rec expand_find = function
	      [] -> []
	    | (((bl, def_list, t, p1) as br1)::r) ->
		let r' = expand_find r in 
		match t.t_desc with
		  FindE(l2, t2, find_info') when Terms.is_false t2 && (is_unique l2 find_info' == Unique) ->
		    let result = 
		      (List.map (fun (bl3, def_list3, t3, t4) ->
			(* Replace references to variables in bl3 with the corresponding 
			   replication indices in t4 (because t4 occurred in the "then" branch
			   before transformation, and occurs in the condition after
			   transformation). 
			   The transformation would be incorrect if t4 tested for the definition
			   of variables in bl3, because these variables are defined more
			   in the initial game than in the transformed game.
			   However, this cannot happen because variables of bl3 are defined
			   in the condition of a find, so there are no array accesses on them. *)
			let t4' = Terms.subst3 (List.map (fun (b,b') -> (b, Terms.term_from_repl_index b')) bl3) t4 in
			(* The variables in bl3 are no longer used, but I need to have some variables there.
			   Moreover, the old variables of bl3 cannot be kept, because their
			   args_at_creation is not correct in the transformed game *)
			let bl3' = List.map (fun (b,b') -> (Terms.create_binder b.sname (Terms.new_vname()) b.btype cur_array, b')) bl3 in
			(bl @ bl3', def_list @ def_list3, make_and_find_cond t3 t4', p1)) l2) @ r'
		    in
		    done_expand := true;
		    current_pass_transfos := (SFindinFindCondition(p',t)) :: (!current_pass_transfos);
		    result
		| _ -> br1 :: r'
	  in
	  expand_find l0
	  with CannotExpand -> l0
	else
	  l0
      in
      if (!done_expand) then
	begin
	  Settings.changed := true;
	  let find_info = is_unique l0' find_info in
	  Terms.oproc_from_desc2 p' (Find(l0', p2, find_info))
	end
      else

      (* Expand find in branch of find when both finds are "unique"
	 TO DO I could perform several of these transformations in a single step,
	 but I'm not sure if I want to have many nested Finds in the else branch *)
      let l0', p2' = 
	if (!Settings.unique_branch_reorg) then
	  try
	  let rec expand_find seen = function
	      [] -> l0, p2
	    | (((bl, def_list, t, p1) as br1)::r) ->
		match p1.p_desc with
		  Find(l3, p3, Unique) when (find_info == Unique) ->
		    List.iter (fun (b,_) ->
		      Settings.advise := Terms.add_eq (SArenaming b) (!Settings.advise)) bl;
		    let result = 
		      (List.rev_append seen ((List.concat (List.map (generate_branches br1) l3)) @ r)),
		      (Terms.oproc_from_desc (Find([bl, def_list, t, p3], p2, Unique)))
		    in
		    current_pass_transfos := (SFindinFindBranch(p',p1)) :: (!current_pass_transfos);
		    result
		| _ -> expand_find (br1::seen) r
	  in
	  expand_find [] l0
	  with CannotExpand -> l0, p2
	else
	  l0, p2
      in
      if l0' != l0 then
	begin
	  Settings.changed := true;
	  let find_info = is_unique l0' find_info in
	  Terms.oproc_from_desc2 p' (Find(l0', p2', find_info))
	end
      else

      match l0 with
	[] ->
	  simplify_oprocess cur_array dep_info true_facts p2
      |	[([],def_list,t1,p1)] when (Facts.reduced_def_list p'.p_facts def_list = []) && 
	                              (match t1.t_desc with Var _ | FunApp _ -> true | _ -> false) -> 
	  Settings.changed := true;
	  current_pass_transfos := (SFindtoTest p') :: (!current_pass_transfos);
	  simplify_oprocess_modified cur_array dep_info true_facts p_orig (Terms.oproc_from_desc2 p'  (Test(t1,p1,p2)))
      |	_ -> 

      let def_vars = Facts.get_def_vars_at p'.p_facts in
      let p2' = 
	if p2.p_desc == Yield then Terms.oproc_from_desc Yield else
	try
	  simplify_oprocess cur_array dep_info_else (add_elsefind (dependency_collision cur_array dep_info_else) def_vars true_facts l0) p2
	with Contradiction ->
	  Settings.changed := true;
	  current_pass_transfos := (SFindElseRemoved(p')) :: (!current_pass_transfos);
	  Terms.oproc_from_desc Yield
      in
      let rec simplify_findl dep_info_l1 l1 = 
	match (dep_info_l1,l1) with
	  [],[] -> []
	| (dep_info_cond::dep_info_then::dep_info_l),((bl, def_list, t, p1)::l) ->
	    begin
	    let l' = simplify_findl dep_info_l l in
	    let vars = List.map fst bl in
	    let repl_indices = List.map snd bl in
	    let cur_array_cond = repl_indices @ cur_array in
	    let vars_terms = List.map Terms.term_from_binder vars in
	    try
	      let this_branch_node = Facts.get_node p'.p_facts in 
	      let def_list' = Facts.reduced_def_list p'.p_facts def_list in
	      let def_vars_cond = Facts.def_vars_from_defined this_branch_node def_list' in
	      let true_facts = filter_elsefind (Terms.not_deflist_l vars) true_facts in
	      let facts_def_list = Facts.facts_from_defined this_branch_node def_list in
	      let true_facts_t = Facts.simplif_add_list (dependency_collision cur_array_cond dep_info_cond) true_facts facts_def_list in
	      let facts_from_elsefind_facts =
		if !Settings.elsefind_facts_in_simplify then
		  let def_vars_cond' = Terms.union_binderref def_vars_cond def_vars in
		  Simplify1.get_facts_of_elsefind_facts (!whole_game) cur_array_cond true_facts_t def_vars_cond'
		else
		  []
	      in
	      let true_facts_t = Facts.simplif_add_list (dependency_collision cur_array_cond dep_info_cond) true_facts_t facts_from_elsefind_facts in
	      (* Set priorities of variables defined by this find, 
	         to orient rewrite rules preferably in the direction
	         b[..] -> t where b \in bl *)
	      incr current_max_priority;
	      List.iter (fun b -> 
		b.priority <- (!current_max_priority);
		priority_list := b :: (!priority_list)) vars;
	      let (t', facts_cond) =
		match t.t_desc with
		  Var _ | FunApp _ ->
		    let t' = simplify_term cur_array_cond dep_info_cond false true_facts_t t in
		    (t', t' :: facts_from_elsefind_facts @ facts_def_list)
		| _ -> 
		    let t' = simplify_term_w_find cur_array_cond true_facts_t t in
		    (t', facts_from_elsefind_facts @ facts_def_list)
	      in

	      (* [facts_cond] contains the facts that hold,
		 using repl_indices as indices. We substitute vars from them to obtain
		 the facts that hold in the then branch.
		 Same substitution for the dependency info. *)
	      let facts_cond' = List.map (Terms.subst repl_indices vars_terms) facts_cond in
	      let tf' = Facts.simplif_add_list (dependency_collision cur_array dep_info_then) true_facts facts_cond' in

	      (* Check that the "defined" conditions can hold,
		 if not remove the branch *)
	      (* [def_vars_cond] contains the variables that are certainly defined 
		 using repl_indices as indices. We substitute vars from them to obtain
		 the variables certainly defined in the then branch. *)
	      let def_vars_accu = Terms.subst_def_list repl_indices vars_terms def_vars_cond in
	      (* check_compatible_deflist checks that the variables in def_vars_accu can be defined
	         at the current program point *)
	      if not (CompatibleDefs.check_compatible_deflist (CompatibleDefs.Process p_orig) cur_array tf' p'.p_facts def_vars_accu) then
		raise Contradiction;
	      (* check_compatible2_deflist checks that all pairs of variables 
		 that must be defined can be simultaneously defined. 
		 Useful in some examples, but costly! *)
	      let tf' = 
		if !Settings.detect_incompatible_defined_cond then
		  let new_facts = CompatibleDefs2.check_compatible2_deflist def_vars def_vars_accu in
		  Facts.simplif_add_list (dependency_collision cur_array dep_info_then) tf' new_facts 
		else tf'
	      in
	      let def_vars' = 
		(* Using def_vars_accu instead of def_list' is more precise *)
		def_vars_accu @ def_vars
	      in
	      let tf' = convert_elsefind (dependency_collision cur_array dep_info_then) def_vars' tf' in
	      
                if (!Settings.debug_simplify) then
                  begin
	            Printf.printf "\n_________________\nOcc = %d : \n" p.p_occ;
	            Facts.display_facts tf'
                  end;

	      let p1' = simplify_oprocess cur_array dep_info_then tf' p1 in

	      (* TO DO instead of taking the intersection with accu_def_list_subterm,
		 I should rather remove the variable references that are already 
		 guaranteed to be defined. (named [defined_refs] in invariants.ml,
		 for instance) However, I would need to compute those here. *)
	      let accu_def_list = ref def_list' in 
	      List.iter (Terms.get_deflist_subterms accu_def_list) facts_def_list;
	      let accu_def_list_subterm = ref [] in
	      List.iter (Terms.close_def_subterm accu_def_list_subterm) (!accu_def_list);
	      let accu_needed = ref [] in
	      Terms.get_deflist_subterms accu_needed t';
	      (* Replace vars with repl_indices in p1', to get the variable
		 references that need to occur in the new def_list *)
	      let bl_rev_subst = List.map (fun (b,b') -> (b, Terms.term_from_repl_index b')) bl in
	      let p1'_repl_indices = Terms.subst_oprocess3 bl_rev_subst p1' in
	      Terms.get_deflist_oprocess accu_needed p1'_repl_indices;
	      let accu_needed_subterm = ref [] in
	      List.iter (Terms.close_def_subterm accu_needed_subterm) (!accu_needed);
	      let needed_occur = 
		(Facts.reduced_def_list p'.p_facts 
		   (Terms.inter_binderref (!accu_needed_subterm) (!accu_def_list_subterm))) in
	      let implied_needed_occur = Facts.def_vars_from_defined None needed_occur in
	      let def_list'' = Terms.setminus_binderref def_list' implied_needed_occur in
	      let def_list3 = Facts.remove_subterms [] (needed_occur @ (Facts.filter_def_list [] def_list'')) in

	      if List.length def_list3 < List.length def_list then
		begin
		  Settings.changed := true;
		  current_pass_transfos := (SFindDeflist(p', def_list, def_list3)) :: (!current_pass_transfos)
		end
	      else if not (Facts.eq_deflists def_list def_list3)  then
		current_pass_transfos := (SFindDeflist(p', def_list, def_list3)) :: (!current_pass_transfos);

	      (* When i = M implied by def_list & t, remove i from bl
		 and substitute M for i *)
	      let keep_bl = ref [] in
	      let subst = ref [] in
	      List.iter (fun (b, b') -> 
		let b_im = Terms.try_no_var tf' (Terms.term_from_binder b) in
		if (List.exists (fun (b', b_im') -> Terms.refers_to b b_im' || Terms.refers_to b' b_im) (!subst)) ||
		   (Terms.refers_to b b_im)
		then
		  keep_bl := (b, b') :: (!keep_bl)
		else
		  subst := (b, b_im) :: (!subst)
					  ) bl;
	      let bl' = !keep_bl in
	      if (!subst) != [] then 
		begin
		  Settings.changed := true;
		  current_pass_transfos := (SFindIndexKnown(p', (bl, def_list, t, p1), !subst)) :: (!current_pass_transfos)
		end;
	      let subst_repl_indices_source = List.map (fun (b,_) -> List.assq b bl) (!subst) in
	      let subst_repl_indices_target = 
		List.map (fun (_, b_im) -> Terms.subst3 bl_rev_subst b_im) (!subst) 
	      in
	      let def_list_tmp = ref [] in
	      List.iter (fun br ->
		Terms.get_deflist_subterms def_list_tmp 
		  (Terms.subst subst_repl_indices_source subst_repl_indices_target (Terms.term_from_binderref br))) def_list3;
	      let def_list3 = !def_list_tmp in 
	      let t' = Terms.update_args_at_creation ((List.map snd bl') @ cur_array) 
		  (Terms.subst subst_repl_indices_source subst_repl_indices_target t') in
	      let p1' = add_let (Terms.subst_oprocess3 (!subst) p1') (!subst) in
	      (* End of "When i = M implied by def_list & t, remove i from bl
		 and substitute M for i"*)

              let find_branch = (bl', def_list3, t', p1') in

              (* If the find is marked "unique", and we can prove that
	         the current branch succeeds, keep only that branch *)
              if (!Settings.unique_branch) &&
		(match t'.t_desc with
		  Var _ | FunApp _ -> true
		| _ -> false)
	      then 
		try 
		  branch_succeeds find_branch (dependency_collision cur_array_cond dep_info_cond) true_facts def_vars;
		  find_branch :: l'
		with SuccessBranch(subst, keep_bl) ->
		  if not (find_info == Unique) then find_branch :: l' else
		  begin
		    (* Subst is a substitution for replication indices,
		       compute the substitution for the corresponding variables *)
		    let subst_repl_indices_source = List.map (fun (_,b,_) -> b) subst in
		    let subst_repl_indices_target = List.map (fun (_,_,b_im) -> b_im) subst in
		    let subst = List.map (fun (b, _, b_im) -> 
		      (b, Terms.subst repl_indices vars_terms b_im)
			) subst 
		    in
		    if List.exists (fun (b, b_im) -> 
		      (List.exists (fun (b', b_im') -> Terms.refers_to b b_im') subst)
			) subst
		    then raise (OneBranchProcess(find_branch));
		    if subst != [] then 
		      begin
			Settings.changed := true;
			current_pass_transfos := (SFindIndexKnown(p', (bl, def_list, t, p1), subst)) :: (!current_pass_transfos)
		      end;
		    let def_list_tmp = ref [] in
		    List.iter (fun br ->
		      Terms.get_deflist_subterms def_list_tmp 
			(Terms.subst subst_repl_indices_source subst_repl_indices_target (Terms.term_from_binderref br))) def_list3;
		    let def_list3 = !def_list_tmp in 
		    let t' = Terms.update_args_at_creation ((List.map snd keep_bl) @ cur_array) 
			(Terms.subst subst_repl_indices_source subst_repl_indices_target t') in
		    let p1' = add_let (Terms.subst_oprocess3 subst p1') subst in
		    raise (OneBranchProcess(keep_bl, def_list3, t', p1'))
		  end
	      else
		find_branch :: l'

	      (*let t_or_and = Terms.or_and_form t' in
	      simplify_find true_facts' l' bl def_list' t_or_and p1 *)
	    with Contradiction ->
	      Settings.changed := true;
	      current_pass_transfos := (SFindBranchRemoved(p',(bl, def_list, t, p1))) :: (!current_pass_transfos);
	      l'
	    end
	| _ -> Parsing_helper.internal_error "Different lengths in simplify/Find"
      in
      try
	let l0' = simplify_findl dep_info_branches l0 in
	if l0' == [] then
	  begin
	    Settings.changed := true;
	    current_pass_transfos := (SFindRemoved(p')) :: (!current_pass_transfos);
	    p2'
	  end
	else
	  begin
	    if (p2'.p_desc == Yield) && (List.for_all (fun (bl,_,t,p1) ->
	      (p1.p_desc == Yield) && (not (List.exists Terms.has_array_ref_q (List.map fst bl)))
		) l0') then
	      begin
		Settings.changed := true;
		current_pass_transfos := (SFindRemoved(p')) :: (!current_pass_transfos);
		Terms.oproc_from_desc Yield
	      end
	    else
	      let find_info = is_unique l0' find_info in
	      Terms.oproc_from_desc2 p' (Find(l0', p2', find_info))
	  end
      with OneBranchProcess(find_branch) ->
	match find_branch with
	  ([],[],_,p1) -> 
	    Settings.changed := true;
	    current_pass_transfos := (SFindSingleBranch(p',find_branch)) :: (!current_pass_transfos);
	    p1
	| _ ->
	    (* the else branch of the find will never be executed *)
	    if (List.length l0 > 1) || (p2.p_desc != Yield) then 
	      begin
		Settings.changed := true;
		current_pass_transfos := (SFindSingleBranch(p',find_branch)) :: (!current_pass_transfos);
	      end;
	    Terms.oproc_from_desc2 p' (Find([find_branch], Terms.oproc_from_desc Yield, find_info))
	
      end
  | Let(pat, t, p1, p2) ->
      begin
      let true_facts' = filter_elsefind (Terms.not_deflist_l (Terms.vars_from_pat [] pat)) true_facts in
      match dep_info_list' with
	[dep_info_in; dep_info_else] ->
	  let t' = simplify_term cur_array dep_info (Terms.is_pat_tuple pat) true_facts t in
	  begin
	    try
	      let true_facts_else =
		try
		  Facts.simplif_add (dependency_collision cur_array dep_info_else) true_facts (Terms.make_for_all_diff (Terms.gen_term_from_pat pat) t) 
		with Terms.NonLinearPattern -> true_facts
	      in
	      simplify_let p_orig p' dep_info_else true_facts_else dep_info dep_info_in cur_array true_facts' p1 p2 t' pat
	    with Contradiction ->
	      if p2.p_desc != Yield then 
		begin
		  Settings.changed := true;
		  current_pass_transfos := (SLetElseRemoved(p')) :: (!current_pass_transfos);
		end;
	      simplify_let p_orig p' dep_info_else true_facts dep_info dep_info_in cur_array true_facts' p1 (Terms.oproc_from_desc Yield) t' pat
	  end
      |	[dep_info_in] -> 
	  let t' = simplify_term cur_array dep_info (Terms.is_pat_tuple pat) true_facts t in
	  simplify_let p_orig p' dep_info true_facts dep_info dep_info_in cur_array true_facts' p1 (Terms.oproc_from_desc Yield) t' pat 
      |	_ -> Parsing_helper.internal_error "Bad dep_info_list' in case Let"
      end
  | Output((c,tl),t2,p) ->
      (* Remove all "Elsefind" facts since variables may be defined 
         between the output and the following input *)
      let (subst, facts, _) = true_facts in
      let true_facts' = (subst, facts, []) in
      Terms.oproc_from_desc2 p' 
	(Output((c, List.map (fun t -> simplify_term cur_array dep_info false true_facts t) tl), 
	     simplify_term cur_array dep_info false true_facts t2,
	     simplify_process cur_array (List.hd dep_info_list') true_facts' p))
  | EventP(t,p) ->
      begin
      match t.t_desc with
	FunApp(f,_) ->
	  if not (Settings.event_occurs_in_queries f (!whole_game).current_queries) then
	    simplify_oprocess cur_array (List.hd dep_info_list') true_facts p
	  else
	    Terms.oproc_from_desc2 p' (EventP(simplify_term cur_array dep_info false true_facts t,
					  simplify_oprocess cur_array (List.hd dep_info_list') true_facts p))
      |	_ ->
	  Parsing_helper.internal_error "Events must be function applications"
      end
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

and simplify_if p_orig if_p dep_info cur_array true_facts ptrue pfalse t' =
  match t'.t_desc with
    FunApp(f, []) when f == Settings.c_false -> 
      Settings.changed := true;
      current_pass_transfos := (STestFalse(if_p)) :: (!current_pass_transfos);
      pfalse
  | FunApp(f, []) when f == Settings.c_true -> 
      Settings.changed := true;
      current_pass_transfos := (STestTrue(if_p)) :: (!current_pass_transfos);
      simplify_oprocess cur_array dep_info true_facts ptrue
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      Settings.changed := true;
      current_pass_transfos := (STestOr(if_p)) :: (!current_pass_transfos);
      simplify_if p_orig if_p dep_info cur_array true_facts ptrue (simplify_if p_orig if_p dep_info cur_array true_facts ptrue pfalse t2) t1
  | _ -> 
      try
	let true_facts' = Facts.simplif_add (dependency_collision cur_array dep_info) true_facts t' in
	(* Check that the variables known to be defined are 
           compatible. This check is useful when the condition
           of "if" shows that some index terms are equal to
	   the current replication indices. *)
	let def_vars_accu = Facts.get_def_vars_at if_p.p_facts in
	if not (CompatibleDefs.check_compatible_deflist (CompatibleDefs.Process p_orig) cur_array true_facts' if_p.p_facts def_vars_accu) then
	  raise Contradiction;
	(* Simplify the "then" branch *)
	let ptrue' =  simplify_oprocess cur_array dep_info true_facts' ptrue in
	if (ptrue'.p_desc == Yield) && (pfalse.p_desc == Yield) then 
	  begin
	    Settings.changed := true;
	    current_pass_transfos := (STestMerge(if_p)) :: (!current_pass_transfos);
	    Terms.oproc_from_desc Yield
	  end
	else
	  Terms.oproc_from_desc2 if_p (Test(t', ptrue', pfalse))
      with Contradiction ->
	Settings.changed := true;
	current_pass_transfos := (STestFalse(if_p)) :: (!current_pass_transfos);
	pfalse

(*
and simplify_find true_facts accu bl def_list t' ptrue = 
  match t'.t_desc with
    FunApp(f, []) when f == Settings.c_false -> 
      Settings.changed := true;
      accu
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      Settings.changed := true;
      simplify_find true_facts (simplify_find true_facts accu bl def_list t2 ptrue) bl def_list t1 ptrue
  | _ -> 
      try
	let tf' = Facts.simplif_add true_facts t' in
	(bl, def_list, t', simplify_oprocess tf' ptrue) :: accu
      with Contradiction ->
	Settings.changed := true;
	accu
*)

and simplify_let p_orig let_p dep_info_else true_facts_else dep_info dep_info_in cur_array true_facts ptrue pfalse t' = function
    (PatVar b) as pat -> 
      if pfalse.p_desc != Yield then 
	begin
	  Settings.changed := true;
	  current_pass_transfos := (SLetElseRemoved(let_p)) :: (!current_pass_transfos);	  
	end;
      begin
	try
	  Terms.oproc_from_desc2 let_p 
	    (Let(pat, t', simplify_oprocess cur_array dep_info_in 
		   (Facts.simplif_add (dependency_collision cur_array dep_info_in) true_facts 
		      (Terms.make_let_equal (Terms.term_from_binder b) t')) ptrue, Terms.oproc_from_desc Yield))
	with Contradiction -> 
	  Parsing_helper.internal_error "adding b = pat should not yield a contradiction"
      end
  | (PatEqual t) as pat ->
      Settings.changed := true;
      current_pass_transfos := (SLetSimplifyPattern(let_p, pat, DEqTest)) :: (!current_pass_transfos);
      simplify_oprocess_modified cur_array dep_info true_facts p_orig
	(Terms.oproc_from_desc2 let_p (Test(Terms.make_equal t t', ptrue, pfalse)))
  | (PatTuple (f,l)) as pat ->
      begin
	try 
	  let res = simplify_oprocess_modified cur_array dep_info true_facts 
	      p_orig (Terms.put_lets l (Terms.split_term f t') ptrue pfalse)
	  in
	  Settings.changed := true;
	  current_pass_transfos := (SLetSimplifyPattern(let_p, pat, DExpandTuple)) :: (!current_pass_transfos);
	  res
	with 
	  Not_found -> 
	    begin
	      try
		let ptrue' = simplify_oprocess cur_array dep_info_in (Facts.simplif_add (dependency_collision cur_array dep_info_in) true_facts 
		   (Terms.make_equal (Terms.term_from_pat pat) t')) ptrue
		in
		if (ptrue'.p_desc == Yield) && (pfalse.p_desc == Yield) &&
		  (not (needed_vars_in_pat pat)) then
		  begin
		    Settings.changed := true;
		    current_pass_transfos := (SLetRemoved(let_p)) :: (!current_pass_transfos);
		    Terms.oproc_from_desc Yield
		  end
		else
		  Terms.oproc_from_desc2 let_p (Let(pat, t', ptrue', simplify_oprocess cur_array dep_info_else true_facts_else pfalse))
	      with Contradiction ->
		Settings.changed := true;
		current_pass_transfos := (SLetRemoved(let_p)) :: (!current_pass_transfos);
		simplify_oprocess cur_array dep_info_else true_facts_else pfalse
	    end
	| Terms.Impossible -> 
	    Settings.changed := true;
	    current_pass_transfos := (SLetSimplifyPattern(let_p, pat, DImpossibleTuple)) :: (!current_pass_transfos);
	    simplify_oprocess cur_array dep_info_else true_facts_else pfalse
      end

let rec simplify_main1 iter g =
  let tmp_changed = !Settings.changed in
  current_pass_transfos := [];
  partial_reset g;
  Settings.changed := false;
  Terms.array_ref_process g.proc;
  Terms.build_def_process None g.proc;
  Terms.build_compatible_defs g.proc;
  try
    let p' = simplify_process [] DepAnal2.init ([],[],[]) g.proc in
    let current_transfos = !current_pass_transfos in
    current_pass_transfos := [];
    Terms.cleanup_array_ref();
    Terms.empty_comp_process g.proc;
  (* I need to apply auto_sa_rename because I duplicate some code
     (for example when there is an || inside a test, or when
     I reorganize a find inside a condition of find). I may then
     duplicate assignments to variables inside conditions of find,
     and thus break the invariant that these variables have a single
     definition. auto_sa_rename restores this invariant.
   *)
    if !Settings.changed then
        let (g',proba_sa_rename, renames) = Transf_auto_sa_rename.auto_sa_rename { proc = p'; game_number = -1; current_queries = g.current_queries } in
        if iter != 1 then 
	  let (g'', proba'', renames'') = simplify_main1 (iter-1) g' in
          (g'', proba'' @ proba_sa_rename, renames'' @ renames @ [DSimplify(current_transfos)])
        else
	  begin
            print_string "Run simplify ";
            print_int ((!Settings.max_iter_simplif) - iter + 1);
            print_string " time(s). Maximum reached.\n";
            (g',proba_sa_rename,renames @ [DSimplify(current_transfos)])
          end
    else
	begin
	  print_string "Run simplify ";
          print_int ((!Settings.max_iter_simplif) - iter + 1);
	  print_string " time(s). Fixpoint reached.\n";
          Settings.changed := tmp_changed;
	  (g,[],[])
	end
  with Restart (b,g') ->
    Terms.cleanup_array_ref();
    Terms.empty_comp_process g.proc;
    let (res, proba, transfos) = simplify_main1 iter g' in
    (res, proba, transfos @ [DGlobalDepAnal(b, !Proba.elim_collisions_on_password_occ)])

let simplify_main coll_elim g =
  reset coll_elim g;
  let (res_game, proba_sa_rename, renames) = simplify_main1 (!Settings.max_iter_simplif) g in
  (* Transfer the local advice of Globaldepanal to the global advice in Settings.advise *)
  List.iter (fun x -> Settings.advise := Terms.add_eq x (!Settings.advise)) (!Transf_globaldepanal.advise);
  Transf_globaldepanal.advise := [];
  (* Add probability for eliminated collisions *)
  let proba = final_add_proba() in
  (res_game, proba @ proba_sa_rename, renames)
