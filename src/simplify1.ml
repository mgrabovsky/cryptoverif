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

(* Create fresh replication indices *)

let repl_index_counter = ref 0
(* mapping from terms to fresh repl indexes *)
let repl_index_list = ref []

let new_repl_index_term t =
  let rec find_repl_index = function
      [] ->
	incr repl_index_counter;
	let b' = Terms.create_repl_index "!2" (!repl_index_counter) t.t_type in
	repl_index_list := (t,b') :: (!repl_index_list);
	b'
    | ((a,b')::l) ->
	if Terms.equal_terms a t then b' else
	find_repl_index l
  in
  find_repl_index (!repl_index_list)

let new_repl_index b = new_repl_index_term (Terms.term_from_repl_index b)

(* An element (t1, t2, b, lopt, T) in term_collisions means that
the equality t1 = t2 was considered impossible; it has
negligible probability because t1 depends on b[lopt] by decompos followed
by compos functions, the types T are the types obtained after applying
the decompos functions (they are large types), and t2 does not depend 
on b *)

let term_collisions = ref []

let reset coll_elim g =
  Proba.reset coll_elim g;
  term_collisions := [];
  repl_index_list := []


let any_term_name = "?"
let any_term_binder t = 
  let b' = Terms.create_binder any_term_name 0 t [] in
  let rec node = { above_node = node;
		   binders = [b'];
		   true_facts_at_def = [];
		   def_vars_at_def = [];
		   elsefind_facts_at_def = [];
		   future_binders = []; future_true_facts = []; 
		   definition = DNone; definition_success = DNone }
  in
  b'.def <- [node];
  b'

let any_term t = Terms.term_from_binder (any_term_binder t.t_type)

let any_term_pat pat = 
  Terms.term_from_binder (any_term_binder (Terms.get_type_for_pattern pat))

(* Links for replication indices *)

let current_bound_ri = ref []

let ri_link v l =
  current_bound_ri := v :: (!current_bound_ri);
  v.ri_link <- l

let ri_cleanup () =
  List.iter (fun v -> v.ri_link <- NoLink) (!current_bound_ri);
  current_bound_ri := []

let rec cleanup_until l l' = 
  if l' == l then () else
  match l' with
    [] -> Parsing_helper.internal_error "cleanup_until"
  | (v::r) -> 
      v.ri_link <- NoLink;
      cleanup_until l r

let ri_auto_cleanup f =
  let tmp_bound_ri = !current_bound_ri in
  current_bound_ri := [];
  try
    let r = f () in
    List.iter (fun v -> v.ri_link <- NoLink) (!current_bound_ri);
    current_bound_ri := tmp_bound_ri;
    r
  with x ->
    List.iter (fun v -> v.ri_link <- NoLink) (!current_bound_ri);
    current_bound_ri := tmp_bound_ri;
    raise x

let ri_auto_cleanup_failure f =
  let tmp_bound_ri = !current_bound_ri in
  try
    f() 
  with x ->
    cleanup_until tmp_bound_ri (!current_bound_ri);
    current_bound_ri := tmp_bound_ri;
    raise x

(* [get_var_link] function associated to [match_term3].
   See the interface of [Terms.match_funapp] for the 
   specification of [get_var_link]. *)

let get_var_link t () =
  match t.t_desc with
    Var (v,[]) when v.sname==any_term_name -> Some(v.link, true)
  | ReplIndex (v) -> Some(v.ri_link, false)
  | _ -> None
    
let rec match_term3 next_f t t' () = 
  ri_auto_cleanup_failure (fun () ->
    match t.t_desc, t'.t_desc with
      Var (v,[]), _ when v.sname==any_term_name -> next_f()
    | ReplIndex (v), _ -> 
      (* Check that types match *)
	if t'.t_type != v.ri_type then
	  raise NoMatch;
	begin
	  match v.ri_link with
	    NoLink -> ri_link v (TLink t')
	  | TLink t -> if not (Terms.equal_terms t t') then raise NoMatch;
	end;
	next_f()
    | Var(b,l), Var(b',l') when b == b' -> 
	Terms.match_term_list match_term3 next_f l l' ()
    | FunApp(f,l), FunApp(f',l') when f == f' ->
	Terms.match_funapp match_term3 get_var_link Terms.default_match_error Terms.simp_facts_id next_f t t' ()
    | _ -> raise NoMatch
	  )

let matches_pair t1 t2 t1' t2' =
  try
    ri_auto_cleanup (match_term3 (match_term3 (fun () -> ()) t2 t2') t1 t1');
    true
  with NoMatch -> false

let matches_pair_with_order_ass order_assumptions side_condition t1 t2 order_assumptions' side_condition' t1' t2' =
  try 
    if (order_assumptions != []) && (order_assumptions' == []) then
      false
    else
      begin
	match_term3 (match_term3 (match_term3 (fun () -> 
	  let order_assumptions_instance = List.map (fun (br1,br2) ->
	    (Terms.copy_term Terms.Links_RI (Terms.term_from_binderref br1),
	     Terms.copy_term Terms.Links_RI (Terms.term_from_binderref br2))) order_assumptions
	  in
	  let order_assumptions' = List.map (fun (br1, br2) ->
	    (Terms.term_from_binderref br1,
	     Terms.term_from_binderref br2)) order_assumptions'
	  in
	  if not 
	      (List.for_all (fun (br1,br2) ->
		List.exists (fun (br1',br2') ->
		  (Terms.equal_terms br1 br1') && (Terms.equal_terms br2 br2')) order_assumptions') order_assumptions_instance)
	  then raise NoMatch
	      ) side_condition side_condition') t2 t2') t1 t1' ();
	true
      end
  with NoMatch -> false

let eq_terms3 t1 t2 =
  try
    match_term3 (fun () -> ()) t1 t2 ();
    true
  with NoMatch ->
    false

let get_index_size b =
  match b.ri_type.tcat with
    Interv p -> p.psize
  | BitString -> Parsing_helper.internal_error "I would expect indices to have interval type in get_index_size"

let greater_size b1 b2 = compare (get_index_size b2) (get_index_size b1)

(* Filter out the indices that are unique knowing other indices 
   (useful for reducing the probabilities of collision) 

   true_facts must not contain if/let/find/new. 
   if the initial indices contain "noninteractive" indices, we try
   to eliminate them, even by adding "interactive" indices, as follows: 
   we start from a list (initial_indices) of indices that consists of
   (1) the "noninteractive" indices in the initial useful indices
   (2) the "interactive" indices that occur in all_indices but not in the 
      initial useful indices
   (3) the "interactive" indices that occur in the initial indices
   and try to eliminate the indices in order. At each step, we check that all
   indices in the initial useful indices (used_indices) are uniquely 
   determined. 
   *)


let filter_indices_coll true_facts used_indices initial_indices =
  (* Filter the indices *)
  (*print_string "Filter_indices_coll\nKnowing\n";
  List.iter (fun f -> Display.display_term f; print_newline()) true_facts;
  print_string "used_indices: ";
  Display.display_list Display.display_binder used_indices;
  print_string "\ninitial_indices: ";
  Display.display_list Display.display_binder initial_indices;
  print_string "\n";*)
  let useful_indices = ref [] in
  let useless_indices = ref [] in
  (* Remove all indices that are before the first used index.
     Indeed, if we remove those, all used indices are still present,
     so that's clearly sufficient. *)
  let rec remove_first_indices = function
      [] -> []
    | (b::l) -> 
	if not (List.memq b used_indices) then 
	  begin
	    useless_indices := b :: (!useless_indices);
	    remove_first_indices l
	  end
	else
	  b::l
  in
  let initial_indices' = remove_first_indices initial_indices in
  let used_indices_term = List.map Terms.term_from_repl_index used_indices in
  let rec filter_indices_rec = function
      [] -> ()
    | first_index::rest_indices ->
	List.iter (fun b -> 
	  let b' = new_repl_index b in
	  ri_link b (TLink (Terms.term_from_repl_index b')))
	  (first_index::(!useless_indices));
	let true_facts' = List.map (Terms.copy_term Terms.Links_RI) true_facts in
	let used_indices_term' = List.map (Terms.copy_term Terms.Links_RI) used_indices_term in 
	ri_cleanup();
	let diff_fact = Terms.make_or_list (List.map2 Terms.make_diff used_indices_term used_indices_term') in
	let facts = diff_fact :: (true_facts' @ true_facts) in
	try
	  (*print_string "index: "; Display.display_binder first_index; *)
	  ignore (Terms.auto_cleanup (fun () -> Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) facts));
	  (* The index cannot be removed *)
	  (*print_string " kept\n";*)
	  useful_indices := (!useful_indices) @ [first_index];
	  filter_indices_rec rest_indices
	with Contradiction ->
	  (* The index can be removed *)
	  (*print_string " removed\n";*)
	  useless_indices := first_index :: (!useless_indices);
	  filter_indices_rec rest_indices
  in
  filter_indices_rec initial_indices';
  (*print_string "Result: "; Display.display_list Display.display_binder (!useful_indices); print_newline();*)
  if (!useless_indices) == [] then
    (* Removed no index, return the initial list physically, to facilitate
       testing that the list of indices was unchanged *)
    initial_indices
  else    
    (!useful_indices)

(* Collision t1 = t2 means: for all indices in t1, t2 such that true_facts holds, eliminate collision t1 = t2.
   Collision t1' = t2' means: for all indices in t1', t2' such that true_facts' holds, eliminate collision t1' = t2'.
There is a substitution sigma such that
 * t1' = sigma t1', t2' = sigma t2
 * There is a subset common_facts of true_facts suchthat
   true_facts' contains at least sigma common_facts 
 * The same indices can be removed using common_facts as
   using true_facts, so that the used indices at t1 = t2 with common_facts
   are still really_used_indices.
Then we replace both calls with
  for all indices in t1, t2 and common_facts such that common_facts holds, 
  eliminate collision t1 = t2
This is more general than the two collisions and yields the same cardinal 
as t1 = t2. *)

let matches 
    (order_assumptions, side_condition, true_facts, used_indices, initial_indices, really_used_indices, t1, t2, b, lopt, tl)
    (order_assumptions', side_condition', true_facts', used_indices', initial_indices', really_used_indices', t1', t2', b', lopt', tl') =
  ri_auto_cleanup (fun () -> 
    if matches_pair_with_order_ass order_assumptions side_condition t1 t2 order_assumptions' side_condition' t1' t2' then
      let common_facts = List.filter (fun f -> List.exists (fun f' -> eq_terms3 f f') true_facts') true_facts in
      ri_cleanup();
      (* Check that we can remove the same indices using common_facts as with all facts *)
      if initial_indices == really_used_indices then
	(* If we removed no index, this is certainly true *)
	Some(order_assumptions, side_condition, common_facts, used_indices, initial_indices, really_used_indices, t1, t2, b, lopt, tl)
      else
      let really_used_indices'' = filter_indices_coll common_facts used_indices initial_indices in
      if Terms.equal_lists (==) really_used_indices really_used_indices'' then
	begin
	  (*
	  print_string "Simplify.matches ";
	  Display.display_term t1;
	  print_string " with ";
	  Display.display_term t2;
	  print_string " succeeds\n";
	  print_string "Common facts:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) common_facts; *)
	  Some(order_assumptions, side_condition, common_facts, used_indices, initial_indices, really_used_indices, t1, t2, b, lopt, tl)
	end
      else
	begin
	  (*
	  print_string "Simplify.matches ";
	  Display.display_term t1;
	  print_string " with ";
	  Display.display_term t2;
	  print_string " fails\n";
	  print_string "True facts:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) true_facts;
	  print_string "True facts':\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) true_facts';
	  print_string "Common facts:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) common_facts;
	  print_string "used_indices\n";
	  Display.display_list Display.display_binder used_indices;
	  print_newline();
	  print_string "initial_indices\n";
	  Display.display_list Display.display_binder initial_indices;
	  print_newline();
	  print_string "really_used_indices\n";
	  Display.display_list Display.display_binder really_used_indices;
	  print_newline();
	  print_string "really_used_indices''\n";
	  Display.display_list Display.display_binder really_used_indices'';
	  print_newline();*)
	  None
	end
    else
      None)

let add_term_collisions (cur_array, true_facts, order_assumptions, side_condition) t1 t2 b lopt tl =
  (* Add the indices of t1,t2 to all_indices; some of them may be missing
     initially because array indices in t1,t2 that depend on "bad" variables
     are replaced with fresh indices, and these indices are not included in
     cur_array initially (cur_array contains the replication and find
     indices above the considered terms) *)
  let all_indices_ref = ref cur_array in
  Proba.collect_array_indexes all_indices_ref t1;
  Proba.collect_array_indexes all_indices_ref t2;
  let all_indices = !all_indices_ref in
  (* Compute the used indices *)
  let used_indices_ref = ref [] in
  Proba.collect_array_indexes used_indices_ref t1;
  Proba.collect_array_indexes used_indices_ref t2;
  let used_indices = !used_indices_ref in
  try
  let collision_info = 
    (* If the probability used_indices/t for t in tl is small enough to eliminate collisions, return that probability.
       Otherwise, try to optimize to reduce the factor used_indices *)
    if List.for_all (fun t -> 
      Proba.is_small_enough_coll_elim (used_indices, t)
	) tl then 
      (order_assumptions, side_condition, [], used_indices, used_indices, used_indices, t1, t2, b, lopt, tl)
    else
      (* Try to reduce the list of used indices. 
	 The initial list of indices is a reordering of the list of all indices.
	 We start with the larger indices (to eliminate them first) and among
	 the indices of the same size, with those that are not in used_indices
	 (also to eliminate them first).
	 The goal is to try to remove large indices
	 of used_indices, perhaps at the cost of adding more
         smaller indices of all_indices. *)
      let initial_indices =
	  (* Sort used_indices and all_indices in decreasing size *)
	  let used_indices_sort = List.sort greater_size used_indices in
	  let all_indices_sort = List.sort greater_size all_indices in
	  (* Remove elements of all_indices that are in used_indices *)
	  let all_indices_sort_minus_used_indices = List.filter (fun b -> not (List.memq b used_indices_sort)) all_indices_sort in
	  (* Build a list by merging indices from all_indices and used_indices.
	     When indices are of the same size, we put elements of all_indices first,
	     so that they will be eliminated, except if they are now necessary
	     because they replace some larger index eliminated before. *)
	  List.merge greater_size all_indices_sort_minus_used_indices used_indices_sort 
      in
      let really_used_indices = filter_indices_coll true_facts used_indices initial_indices in
      (* OLD: I can forget the facts without losing precision when I removed no index
	 (initial_indices == really_used_indices);
	 Now, if I removed no index, the probability will be too large to eliminate collisions. *)
      if List.for_all (fun t -> 
	Proba.is_small_enough_coll_elim (really_used_indices, t)
	  ) tl then 
	(order_assumptions, side_condition, true_facts, used_indices, initial_indices, really_used_indices, t1, t2, b, lopt, tl) 
      else
	(* Raises NoMatch when the probability is too large to be accepted *)
	raise NoMatch
  in
    (* I remove an entry when another entry is an instance of it,
       obtained by substituting terms for replication indexes *)
  let rec find_more_general_coll = function
      [] -> raise Not_found
    | (collision_info' :: rest) ->
	match matches collision_info' collision_info with
	  Some collision_info'' -> collision_info'' :: rest
	| None -> collision_info' :: (find_more_general_coll rest)
  in
  begin
    try
      term_collisions := find_more_general_coll (!term_collisions)
    with Not_found ->
      let new_coll = ref collision_info in
      let term_collisions' = List.filter (fun collision_info' -> 
	match matches (!new_coll) collision_info' with
	  None -> true
	| Some collision_info'' -> new_coll := collision_info''; false) (!term_collisions)
      in
      term_collisions := (!new_coll) :: term_collisions'
  end;
  true
  with NoMatch -> 
    false

let proba_for_term_collision (order_assumptions, side_condition, _, _, _, really_used_indices, t1, t2, b, lopt, tl) =
  print_string "Eliminated collisions between ";
  Display.display_term t1;
  print_string " and ";
  Display.display_term t2;
  print_string " Probability: ";  
  let nindex = Polynom.p_prod (List.map (fun array_idx -> Proba.card array_idx.ri_type) really_used_indices) in
  let p = 
    match tl with
      [t] -> Proba.pcoll1rand nindex t
    | _ -> Polynom.p_sum (List.map (fun t -> Proba.pcoll1rand nindex t) tl)
  in
  Display.display_proba 0 p;
  print_newline();
  print_string "(";
  if order_assumptions != [] then
    begin
      print_string "assuming ";
      Display.display_list (fun ((b1, l1), (b2, l2)) ->
	Display.display_var b2 l2;
	print_string " is defined before ";
	Display.display_var b1 l1
	  ) order_assumptions;
      print_string ", "
    end;
  if not (Terms.is_true side_condition) then
    begin
      if order_assumptions != [] then print_string "and " else print_string "assuming ";
      Display.display_term side_condition;
      print_string ", "
    end;
  Display.display_term t1;
  print_string " characterizes a part of ";
  begin
  match lopt with
    None ->   Display.display_binder b; print_string "[...]"
  | Some l -> Display.display_var b l 
  end;
  print_string " of type(s) ";
  Display.display_list (fun t -> print_string t.tname) tl;
  print_string ";\n ";
  Display.display_term t2;
  print_string " does not depend on ";
  begin
  match lopt with
    None ->   Display.display_binder b; print_string "[...]"
  | Some l -> Display.display_var b l 
  end;
  print_string ")\n";
  p
  

(* Final addition of probabilities *)

let final_add_proba() =
  Proba.final_add_proba (List.map proba_for_term_collision (!term_collisions))

(* Dependency analysis
   When M1 characterizes a part of x of a large type T
   and M2 does not depend on x, then M1 = M2 fails up to
   negligible probability.
   The module FindCompos defines "characterize"
   The modules Transf_globaldepanal and Transf_simplify.DepAnal2 perform dependency analyses
   Function Transf_simplify.dependency_collision concludes *)

module FindCompos : sig

type status = Compos | Decompos | Any
(* The status is
   - [Compos] when a term [t] is obtained from a variable [b0] by first applying
     poly-injective functions (functions marked [compos]), then
     functions that extract a part of their argument 
     (functions marked [uniform]).
   - [Decompos] when [t] is obtained from [b0] by applying functions
     that extract a part of their argument (functions marked [uniform])
   - [Any] in the other cases *)

type charac_type =
    CharacType of typet
  | CharacTypeOfVar of binder

type 'a depinfo =
   (binder * (status * 'a)) list option * term list
      (* The dependency information has two components (dep, nodep):
	 If dep = Some l where l is a list of (variable, ...), such that it 
	 is guaranteed only variables in this list depend on the considered 
	 variable x[...].
	 If dep = None, we have no information of this kind; any variable 
	 may depend on x.
	 nodep is a list of terms that are guaranteed not to depend on x[l].
	 *)

(* [init_elem] is the empty dependency information *)
val init_elem : 'a depinfo

(* [depends (b, depinfo) t] returns [true] when the term [t]
   may depend on the variable [b]. 
   [depinfo] is the dependency information for variable [b]. *)
val depends : (binder * 'a depinfo) -> term -> bool

(* [is_indep (b, depinfo) t] returns a term independent of [b]
   in which some array indices in [t] may have been replaced with
   fresh replication indices. When [t] depends on [b] by variables
   that are not array indices, it raises [Not_found] *)
val is_indep : (binder * 'a depinfo) -> term -> term

(* [remove_dep_array_index (b, depinfo) t] returns a modified 
   version of [t] in which the array indices that depend on [b]
   are replaced with fresh indices.
   [depinfo] is the dependency information for variable [b].*)
val remove_dep_array_index : (binder * 'a depinfo) -> term -> term

(* [remove_array_index t] returns a modified version of [t] in which
   the array indices that are not replication indices are replaced
   with fresh indices. *) 
val remove_array_index : term -> term

(* [find_compos check (b0, depinfo) ((b,(st,_)) as b_st) t] returns
   [Some(st', c, t')] when it could show that [t] characterizes a part of
   [b] (which itself characterizes a part of [b0]).
   [st'] is the status of [t] (Compos or Decompos; see above their meaning).
   [c] determines the type of the part of [b0] that [t] characterizes.
   [t'] is a modified version of [t] in which the parts that are not useful
   to show that [t] characterizes a part of [b] are replaced with variables [?].
   It returns [None] otherwise.

   [check] is a function that checks the validity of the indices of [b] inside [t]:
   [check b_st l] is called when [l] contains the array indices of [b] in [t];
   it returns [Some(st,c')] when these array indices are accepted; 
   [st] is the status of [b];
   [c'] determines the type of the part of [b0] that [b] characterizes.
   It returns [None] otherwise. *)
val find_compos : ((binder * (status * 'a)) -> term list -> (status * charac_type) option) -> (binder * 'a depinfo) -> (binder * (status * 'a)) -> term -> (status * charac_type * term) option

(* [find_compos_list] is the same as [find_compos] but for a list of variables
   instead of a single variable [((b,(st,_)) as b_st)]. 
   It tries each variable in turn until it finds one for which [find_compos]
   succeeds. *)
val find_compos_list : ((binder * (status * 'a)) -> term list -> (status * charac_type) option) -> (binder * 'a depinfo) -> (binder * (status * 'a)) list -> term -> (status * charac_type * term * binder * 'a) option

end
=
struct

let init_elem = (None, [])

let rec depends ((b, (dep,nodep)) as bdepinfo) t = 
  match t.t_desc with
    FunApp(f,l) -> List.exists (depends bdepinfo) l
  | ReplIndex(b') -> false
  | Var(b',l) ->
      (not (List.exists (Terms.equal_terms t) nodep)) && 
      ((
       ((b == b') || (not (Terms.is_restr b'))) &&
       (match dep with
	 None -> true
       | Some dl -> List.exists (fun (b'',_) -> b'' == b') dl
	  )) || (List.exists (depends bdepinfo) l))
  | _ -> true (*Rough overapproximation of the dependency analysis when
       if/let/find/new occur.
       Parsing_helper.internal_error "If/let/find/new unexpected in DepAnal1.depends"*)

let rec is_indep ((b0, (dep,nodep)) as bdepinfo) t =
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
		Terms.term_from_repl_index (new_repl_index_term t')) l)
	  else
	    raise Not_found
      | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in is_indep")

let rec remove_dep_array_index ((b0, (dep,nodep)) as bdepinfo) t =
  Terms.build_term2 t 
     (match t.t_desc with
	FunApp(f,l) -> FunApp(f, List.map (remove_dep_array_index bdepinfo) l)
      | ReplIndex(b) -> t.t_desc
      |	Var(b,l) ->
	  if (List.exists (Terms.equal_terms t) nodep) then
	    t.t_desc 
	  else 
	    Var(b, List.map (fun t' -> 
	      if depends bdepinfo t' then
		Terms.term_from_repl_index (new_repl_index_term t')
	      else
		t') l)
      | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in remove_dep_array_index")

let rec remove_array_index t =
  Terms.build_term2 t 
     (match t.t_desc with
	FunApp(f,l) -> FunApp(f, List.map remove_array_index l)
      | ReplIndex(b) -> t.t_desc
      |	Var(b,l) ->
	  Var(b, List.map (fun t' ->
	    match t'.t_desc with
	      ReplIndex(b') -> t'
	    | _ -> Terms.term_from_repl_index (new_repl_index_term t')
		  ) l)
      | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in remove_dep_array_index")

let reduced = ref false

(* This is a specialized version of Facts.apply_collisions_at_root_once
   for statements, with try_no_var = Terms.try_no_var_id *)
let rec apply_statements_at_root_once t = function
    [] -> t
  | ([], _, redl, Zero, redr)::other_statements ->
      begin
	try
	  Facts.match_term Terms.simp_facts_id [] (fun () -> 
	    let t' = Terms.copy_term Terms.Links_Vars redr in
	    Terms.cleanup();
	    reduced := true;
	    t'
	      ) redl t ()
	with NoMatch ->
	  Terms.cleanup();
	  apply_statements_at_root_once t other_statements
      end
  | _ -> Parsing_helper.internal_error "statements should always be of the form ([], _, redl, Zero, redr)"

(* Same as Facts.apply_reds but does not apply collisions, and 
   applies statements only at the root of the term *)
let rec apply_eq_statements_at_root t =
  reduced := false;
  let t' = Terms.apply_eq_reds Terms.simp_facts_id reduced t in
  if !reduced then apply_eq_statements_at_root t' else 
  let t' =  
    match t.t_desc with
      FunApp(f,l) -> apply_statements_at_root_once t f.f_statements
    | _ -> t
  in
  if !reduced then apply_eq_statements_at_root t' else t


(* find_compos b t returns true when t characterizes b: only one
value of b can yield a certain value of t *)

type status = Compos | Decompos | Any

type charac_type =
    CharacType of typet
  | CharacTypeOfVar of binder

type 'a depinfo =
  (binder * (status * 'a)) list option * term list

let rec find_decompos_bin check ((b,_) as b_st) b' t t' =
  (Proba.is_large_term t || Proba.is_large_term t') && (t'.t_type == t.t_type) &&
  (match t.t_desc, t'.t_desc with
    Var(b1,l), Var(b1',l') when 
    (b == b1 && b' == b1') || (b == b1' && b' == b1) -> 
      (check b_st l != None) && (check b_st l' != None)
  | FunApp(f,l), FunApp(f',l') when 
      (f.f_options land Settings.fopt_UNIFORM) != 0  && (f == f') ->
      List.exists2 (find_decompos_bin check b_st b') l l'
  | _ -> false)
  
let rec find_compos_bin check ((b,(st,_)) as b_st) b' fact =
  match fact.t_desc with
   FunApp(f,[t1;t2]) when f.f_cat == Equal ->
      begin
      match (t1.t_desc, t2.t_desc) with
      	Var(b1,l1), Var(b2,l2) when (b1 == b && b2 == b') ->
	  if check b_st l2 != None then check b_st l1 else None
      |	Var(b1,l1), Var(b2,l2) when (b1 == b' && b2 == b) -> 
	  if check b_st l1 != None then check b_st l2 else None
      |	(FunApp(f1,l1), FunApp(f2,l2)) when
	(f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	  find_compos_bin_l check b_st b' l1 l2
      |	(FunApp(f1,l1), FunApp(f2,l2)) when
	(f1.f_options land Settings.fopt_UNIFORM) != 0  && f1 == f2 ->
	  if (Proba.is_large_term t1 || Proba.is_large_term t2) && (st = Decompos) && 
	    (List.exists2 (find_decompos_bin check b_st b') l1 l2)
	  then Some (Decompos, CharacType t1.t_type)  else None
      |	_ -> None
      end
  | FunApp(f,[t1;t2]) when f == Settings.f_and ->
      begin
	match find_compos_bin check b_st b' t1 with
	  None -> find_compos_bin check b_st b' t2
	| x -> x
      end
  | _ -> None
    
and find_compos_bin_l check b_st b' l1 l2 =
  match (l1,l2) with
    [],[] -> None
  | (a1::l1,a2::l2) ->
      begin
      match find_compos_bin check b_st b' (apply_eq_statements_at_root (Terms.make_equal a1 a2)) with
	None -> find_compos_bin_l check b_st b' l1 l2
      |	Some(_, charac_type) -> Some(Compos,charac_type)
      end
  | _ -> Parsing_helper.internal_error "Lists of different lengths in find_compos_bin_l"
      
let rec subst depinfo assql t =
  Terms.build_term2 t 
     (match t.t_desc with
        ReplIndex(b) -> ReplIndex(b)
      | Var(b,l) -> Var(
	  (try List.assq b (!assql) with Not_found ->
            (* Do not rename variables that do not depend on the
	       variable argument of find_compos *)
	    if (Terms.is_restr b) (* Restrictions (other than the main variable, which is already present in the association list assql) do not depend on the argument of find_compos *)|| 
	       (match depinfo with
	         (Some dl,tl) ->
		   (not (List.exists (fun (b',_) -> b' == b) dl)) ||
		   (List.exists (Terms.equal_terms t) tl)
	       | (None, tl) -> List.exists (Terms.equal_terms t) tl)
	    then b else 
	    let r = Terms.new_binder b in
	    assql := (b,r)::(!assql);
	    r), List.map (subst depinfo assql) l)
      | FunApp(f,l) -> FunApp(f, List.map (subst depinfo assql) l)
      |	_ -> Parsing_helper.internal_error "If, find, let, and new should not occur in subst")

let rec find_decompos check ((b, _) as b_st) t =
  (Proba.is_large_term t) && 
  (match t.t_desc with
    Var(b',l) when b == b' -> 
      check b_st l != None
  | FunApp(f,l) when (f.f_options land Settings.fopt_UNIFORM) != 0 ->
      List.exists (find_decompos check b_st) l
  | _ -> false)

let rec find_compos check (main_var, depinfo) ((b,(st,_)) as b_st) t =
  if (!Settings.debug_simplif_add_facts) then
    begin
      print_string "find_compos:t=";
      Display.display_term t;
      print_newline ()
    end;

  if st = Any then None else
  match t.t_desc with
    Var(b',l) when b == b' -> 
      begin
	match check b_st l with
	  None -> None
	| Some(st, ch_ty) -> Some(st, ch_ty, t)
      end
  | FunApp(f,l) when (f.f_options land Settings.fopt_COMPOS) != 0 ->
      begin
	match find_compos_l check (main_var, depinfo) b_st l with
	  None -> None
	| Some(st, ch_ty, l') -> 
	    Some(st, ch_ty, Terms.build_term2 t (FunApp(f,l')))
      end
  | FunApp(f,l) when (f.f_options land Settings.fopt_UNIFORM) != 0 ->
      if (Proba.is_large_term t) && (st = Decompos) && 
	(List.exists (find_decompos check b_st) l)
      then Some (Decompos, CharacType t.t_type, t)  else None
  | Var _ -> None
  | _ -> 
      (* In a simpler version, we would remove 
	 find_compos_bin, find_compos_bin_l, find_decompos_bin, subst,
	 apply_statement2, apply_all_red2, apply_statements
	 and replace this case with None
	 *)
      let vcounter = !Terms.vcounter in
      let b' = Terms.new_binder b in
      let init_subst = 
	if main_var == b then 
	  [(b,b')] 
	else
	  [(main_var, Terms.new_binder main_var); (b,b')]
      in
      let t' = subst depinfo (ref init_subst) t in
      if (!Settings.debug_simplif_add_facts) then
        begin
          print_string "_->b'=";
          Display.display_binder b';
          print_string ", t'=";
          Display.display_term t';
          print_string ", depinfo=";
          print_newline ()
        end;

      let f1 = apply_eq_statements_at_root (Terms.make_equal t t') in
      let r = 
	match find_compos_bin check b_st b' f1 with
	  None -> None
	| Some(st,ch_ty) -> Some(st, ch_ty, t)
      in
      Terms.vcounter := vcounter; (* Forget created variables *)
      r

and find_compos_l check var_depinfo b_st = function
    [] -> None
  | (a::l) ->
      match find_compos check var_depinfo b_st a with
	None -> 
	  begin
	    match find_compos_l check var_depinfo b_st l with
	      None -> None
	    | Some(st, charac_type, l') -> Some(st, charac_type, (any_term a)::l')
	  end
      |	Some(_, charac_type, a') -> Some(Compos,charac_type, a'::List.map any_term l)

let find_compos_list check var_depinfo seen_list t =
  let rec test_l = function
    [] -> None
  | (((b, (st, x)) as b_st)::l) -> 
      match find_compos check var_depinfo b_st t with
	None -> test_l l
      |	Some(st,charac_type,t') -> Some(st,charac_type,t',b,x)
  in
  test_l seen_list

end




let rec match_term2 next_f simp_facts bl t t' =
  match t.t_desc with
    ReplIndex(v) when (List.memq v bl) ->
      begin
	if t'.t_type != v.ri_type then
	  raise NoMatch;
	match v.ri_link with
	  NoLink -> ri_link v (TLink t')
	| TLink t -> if not (Terms.simp_equal_terms simp_facts true t t') then raise NoMatch
      end;
      next_f ()
  | ReplIndex(v) ->
      begin
	match t'.t_desc with
	  ReplIndex(v') when v == v' -> next_f()
	| _ -> raise NoMatch
      end
  | Var(v,l) ->
      begin
	match t'.t_desc with
	  Var(v',l') when v == v' ->
	    match_term_list2 next_f simp_facts bl l l'
	| _ -> raise NoMatch
      end
  | FunApp _ ->
      Parsing_helper.internal_error "Function symbol in Simplify1.match_term2. Should never occur since it is used to match binderrefs only"
  | _ -> Parsing_helper.internal_error "If, find, let, and new should not occur in match_term2"

and match_term_list2 next_f simp_facts bl l l' = 
  match l,l' with
    [],[] -> next_f()
  | a::l,a'::l' ->
      match_term2 (fun () -> match_term_list2 next_f simp_facts bl l l') 
	simp_facts bl a a'
  | _ -> Parsing_helper.internal_error "Different lengths in match_term_list2"


let match_binderref2 next_f simp_facts bl (b,l) (b',l') =
  if b != b' then raise NoMatch;
  match_term_list2 next_f simp_facts bl l l'

let rec match_among next_match simp_facts bl br = function
    [] -> raise NoMatch
  | (br1::brl) ->
      try 
	ri_auto_cleanup (fun () ->
	  match_binderref2 next_match simp_facts bl br br1)
      with NoMatch ->
	match_among next_match simp_facts bl br brl

let rec match_among_list next_match simp_facts bl def_vars = function
    [] -> next_match()
  | (br1::brl) ->
      match_among (fun () -> 
	match_among_list next_match simp_facts bl def_vars brl) 
	simp_facts bl br1 def_vars
  

let final_next dep_info bl true_facts t () =
  let t' = Terms.copy_term Terms.Links_RI t in
  (* Cleanup links, with possibility to restore *)
  let tmp_list = List.map (fun b -> b.ri_link) bl in
  List.iter (fun b -> b.ri_link <- NoLink) bl;
  (* Raise Contradiction when t implied *)
  ri_auto_cleanup (fun () -> 
    (* TO DO It would be possible to improve this when t' is the conjunction
       of terms in tl:
       replace true_facts := Facts.simplif_add (!true_facts) (Terms.make_not t') with
       if List.for_all (fun t -> 
         try
           ignore(Facts.simplif_add true_facts (Terms.make_not t));
           false
         with Contradiction -> true) tl then raise Contradiction *)
    (* print_string "Adding ";
    Display.display_term (Terms.make_not t');
    print_newline();*)
    true_facts := Facts.simplif_add dep_info (!true_facts) (Terms.make_not t'));
  (* Restore links *)
  List.iter2 (fun b l -> b.ri_link <- l) bl tmp_list;
  (* Backtrack *)
  raise NoMatch

let always_true_def_list_t dep_info bl simp_facts t def_vars def_list =
  try
    match_among_list (final_next dep_info bl simp_facts t) (!simp_facts) bl def_vars def_list
  with NoMatch -> ()

(* Test if a branch of find always succeeds *)

exception SuccessBranch of (binder * repl_index * term) list * (binder * repl_index) list

let final_next2 dep_info bl true_facts t1 () =
  let bl' = List.map snd bl in
  let t1' = Terms.copy_term Terms.Links_RI t1 in
  (* Cleanup links, with possibility to restore *)
  let tmp_list = List.map (fun b -> b.ri_link) bl' in
  List.iter (fun b -> b.ri_link <- NoLink) bl';
  (* Raise Contradiction when t1 implied *)
  begin
    try 
      ri_auto_cleanup (fun () -> 
	ignore (Facts.simplif_add dep_info true_facts (Terms.make_not t1')))
    with Contradiction ->
      (* For the value of bl computed in the links, t1 is true;
	 furthermore match_among_list has checked that all variables
	 in def_list are defined, so this branch of find succeeds *)
      (* print_string "Proved ";
         Display.display_term t1';
         print_newline();*)
      let subst = ref [] in
      let keep_bl = ref [] in
      List.iter2 (fun (b,b') l -> 
	match l with
	  TLink b_im -> subst := (b,b',b_im) :: (!subst)
	| NoLink -> keep_bl := (b,b') :: (!keep_bl)) bl tmp_list;
      raise (SuccessBranch(!subst, !keep_bl))
  end;
  (* Restore links *)
  List.iter2 (fun b l -> b.ri_link <- l) bl' tmp_list;
  (* Backtrack *)
  raise NoMatch

(* Raises SuccessBranch when the branch is proved to succeed for some
   value of the indices. These values are stored in the argument of SuccessBranch *)

let branch_succeeds ((bl, def_list, t1, _): 'b findbranch) dep_info true_facts def_vars =
  let bl'' = List.map snd bl in
  try
    match_among_list (final_next2 dep_info bl true_facts t1) true_facts bl'' def_vars def_list
  with NoMatch -> ()

(* Treatment of elsefind facts *)

let rec add_elsefind dep_info def_vars ((subst, facts, elsefind) as simp_facts) = function
    [] -> simp_facts
  | (((bl, def_list, t1,_):'a findbranch)::l) -> 
      (* When the condition t1 contains if/let/find/new, we simply ignore it when adding elsefind facts. *)
      let simp_facts' = 
	match (bl, def_list, t1.t_desc) with
	  [],[],(Var _ | FunApp _) -> Facts.simplif_add dep_info simp_facts (Terms.make_not t1)
	| _,[],_ -> simp_facts
	| _,_,(Var _ | FunApp _) -> 
	    let bl' = List.map snd bl in
	    let simp_facts_ref = ref (subst, facts, (bl', def_list, t1)::elsefind) in
	    always_true_def_list_t dep_info bl' simp_facts_ref t1 def_vars def_list;
	    !simp_facts_ref
	| _ -> simp_facts
      in
      add_elsefind dep_info def_vars simp_facts' l

let filter_elsefind f (subst, facts, elsefind) =
  (subst, facts, List.filter f elsefind)

let convert_elsefind dep_info def_vars ((subst, facts, elsefind) as simp_facts) =
  let simp_facts_ref = ref simp_facts in
  List.iter (fun (bl, def_list, t1) ->
    always_true_def_list_t dep_info bl simp_facts_ref t1 def_vars def_list
      ) elsefind;
  !simp_facts_ref


let true_facts_from_simp_facts (facts, subst, else_find) =
  subst @ facts

let rec try_no_var_rec simp_facts t =
  let t' = Terms.try_no_var simp_facts t in(* Risk of non-termination? *)
  match t'.t_desc with
    FunApp(f,l) -> 
      Terms.build_term2 t' (FunApp(f, List.map (try_no_var_rec simp_facts) l))
  | _ -> t'


(* Reasoning that depends on assumptions on the order of definition
   of variables. *)

(* [is_in_bl bl t] returns true when the term [t] is equal to some
   variable in the list [bl] *)

let is_in_bl bl t =
  match t.t_desc with
    Var(b,l) ->
      (List.memq b bl) && (Terms.is_args_at_creation b l)
  | _ -> false

(* Dependency analysis that takes into account assumption on the
   definition order

   dep_info = (list of array ref defined later; list of array ref defined before)
 *)

let rec dependency_collision_rec2bis cur_array true_facts order_assumptions ((defl_after, defl_before) as dep_info) t1 t2 t =
  match t.t_desc with
    Var(b,l) when (Terms.is_restr b) && (Terms.mem_binderref (b,l) defl_after) && (Proba.is_large_term t) ->
      begin
        if (!Settings.debug_elsefind_facts) then
          begin
            print_string "t t1 t2="; 
	    Display.display_term t;print_string ", "; 
	    Display.display_term t1;print_string ", ";
	    Display.display_term t2;
          end;
          
        let t' = FindCompos.remove_dep_array_index (b,(None, defl_before)) t in
        let l_after' = 
	  match t'.t_desc with
	    Var (_,l_after') -> l_after'
	  | _ -> Parsing_helper.internal_error "t' must be a variable in dependency_collision_rec2bis"
	in
          if (!Settings.debug_elsefind_facts) then
            begin
              Display.display_term t;print_string " is restriction.";
	      print_newline ();
            end;
	let t1' = FindCompos.remove_dep_array_index (b,(None, defl_before)) t1 in
          if (!Settings.debug_elsefind_facts) then
            begin
              print_string "remove_dep_array_index t1=";
	      Display.display_term t1';print_newline ()
            end;
	let check (b, (st, _)) l =
          if (!Settings.debug_elsefind_facts) then
            begin
              print_string "check: b="; Display.display_binder b; 
	      print_string ", l=";Display.display_list Display.display_term l;
	      print_string ", l_after'=";Display.display_list Display.display_term l_after';
	      print_newline ()
            end;
	  if List.for_all2 Terms.equal_terms l l_after' then
	    Some (st, FindCompos.CharacType b.btype)
	  else
	    None
	in
	match FindCompos.find_compos check (b, (None, defl_before)) (b,(FindCompos.Decompos, b.btype)) t1' with
	  Some(_, FindCompos.CharacType charac_type, t1'') -> 
	    begin
	    try 
              if (!Settings.debug_elsefind_facts) then
                begin
                  print_string "FindCompos ok";print_newline ()
                end;
	      let t2' = FindCompos.is_indep (b, (None, defl_before)) t2 in
	      (* add probability, if small enough. returns true if proba small enough, false otherwise *)
	      add_term_collisions (cur_array, true_facts, order_assumptions, Terms.make_true()) t1'' t2' b (Some l_after') [charac_type]
	    with Not_found -> false
	    end
	| Some _ -> Parsing_helper.internal_error "CharacTypeOfVar should not be used in DepAnal2"
	| None -> false
      end 
  | FunApp(f,l) ->
      List.exists (dependency_collision_rec2bis cur_array true_facts order_assumptions dep_info t1 t2) l
  | _ -> false

(* Dependency analysis taking into account the order of definition of the variables. 
   Here dep_info is a list of array ref defined after and a list of array ref defined before *)

let dependency_collision_order_hyp cur_array order_assumptions dep_info simp_facts t1 t2 =
  let t1' = try_no_var_rec simp_facts t1 in
  let t2' = try_no_var_rec simp_facts t2 in
  let true_facts = true_facts_from_simp_facts simp_facts in
  if (!Settings.debug_elsefind_facts) then
    begin
      print_string "dependency_collision_order_hyp: ";
      Display.display_term t1; print_string ", ";
      Display.display_term t2; print_newline ();
      print_string "simplified t1,t2=";
      Display.display_term t1'; print_string ", ";
      Display.display_term t2'; print_newline ();
    end;
  let b =   
    (dependency_collision_rec2bis cur_array true_facts order_assumptions dep_info t1' t2' t1') ||
    (dependency_collision_rec2bis cur_array true_facts order_assumptions dep_info t2' t1' t2')
  in
  if (!Settings.debug_elsefind_facts) then
    begin
      print_string (if b then "Result: true" else "Result: false");
      print_newline ()
    end;
  if b then Some (Terms.make_false()) else None

(* [above_input_node n] returns the first node corresponding to
   an input above [n]. *)

let rec above_input_node n =
  if n.above_node == n then
    Parsing_helper.internal_error "reached beginning of program without seeing an input";
  match n.definition with
    DInputProcess _ -> n
  | _ -> above_input_node n.above_node
    
(* get_elsefind_facts *)

(* this function returns the list of all the binderref that are defined before the node `node' after transformation through the rename_br transformation, and stops if it encounters a binder from stop_binders or if the node is stop_node *)

let rec add_vars_until_binder_or_node node stop_binders stop_node acc =
  if (node == node.above_node) then
    (
      if (!Settings.debug_elsefind_facts) then
        begin
          print_string "Bug ?";
          print_newline ()
        end;
      acc
    )
  else
  if (node == stop_node) then
    (
      if (!Settings.debug_elsefind_facts) then
        begin
          print_string "Elsefind_fact add_vars stopped at input_node";
          print_newline ()
        end;
      acc
    )
  else if (List.exists (fun b -> List.mem b node.binders) stop_binders) then
      (
        if (!Settings.debug_elsefind_facts) then
          begin
            print_string "Elsefind_fact add_vars stopped because var b or br found";
            print_newline ()
          end;
        acc
      )
  else
    (add_vars_until_binder_or_node node.above_node stop_binders stop_node (node.binders @ acc))
  

(* this function is used as the final function for match_among_list *)
let final_next3 bl def_list t result () =
  ri_auto_cleanup (fun () ->
    let t' = Terms.copy_term Terms.Links_RI t in
    let def_list' = Terms.copy_def_list Terms.Links_RI def_list in
    result := (def_list', t')::(!result));
  (* Backtrack *)
  raise NoMatch

let final_next4 bl def_list t fact_accu () =
  ri_auto_cleanup (fun () ->
    let t' = Terms.copy_term Terms.Links_RI t in
    fact_accu := (Terms.make_not t')::(!fact_accu));
  (* Backtrack *)
  raise NoMatch

(* [get_fact_of_elsefind_fact] collects terms that are true, where
   - the variable b[tl] is known to be defined at the current program point (due to some defined condition of find)
   - the variable b is defined in the else branch of a find, so that 
     [elsefind_fact = (bl,def_list,t1)], which means [forall bl, not (defined(def_list) && t1)] 
     holds just before the definition of b
   - [cur_array] contains the current replication indices
   - [def_vars] are variables known to be defined at the current program point.
   - [simp_facts] are facts known to be true at the current program point.

   - [term_accu] stores the proved terms
   - [g] is the current game

   [get_fact_of_elsefind_fact] uses the following reasoning:
   * we substitute tl for b.args_at_creation in the [elsefind_fact], and choose the variables bl such that
   the elements of def_list are defined at the current program point.
   * then, we know that not (defined(def_list) && t1) holds just before the definition of b[tl].
   * if the elements of def_list are defined before b[tl], we obtain not(t1).
   * otherwise, we try to show that, if an element of def_list is defined after b[tl], then
   t1 leads to a contradiction.
   * if this succeeds, we can conclude that not(t1) holds in all cases.
*)

let defined_after b b1 =
  List.for_all (fun n -> List.memq b1 (Terms.add_def_vars_node [] n)) b.def

let rec add_latest ((b,tl) as br) elsefind = function
    [] -> [(br,elsefind)]
  | ((b', tl') as br',elsefind')::l ->
      if (Terms.equal_elsefind_facts elsefind elsefind') && (Terms.equal_term_lists tl tl') then
	if defined_after b b' then
	  (br,elsefind)::l
	else
	  (br',elsefind')::l
      else
	(br',elsefind')::(add_latest br elsefind l)

let rec collect_eff = function
    [] -> []
  | br::l ->
      let last_effl = collect_eff l in
      let new_effl = 
	try 
          Terms.intersect_list Terms.equal_elsefind_facts (List.map (fun n -> n.elsefind_facts_at_def) (fst br).def)
	with Contradiction -> []
      in
      List.fold_right (add_latest br) new_effl last_effl

let get_fact_of_elsefind_fact term_accu g cur_array def_vars simp_facts (b,tl) ((bl,def_list,t1) as elsefind_fact) =
  if (!Settings.debug_elsefind_facts) then
    begin
      print_string "-----------------\n";
      print_string "Variables known to be currently defined: ";
      Display.display_list (fun (b,tl) -> Display.display_var b tl) def_vars;
      print_newline();
      print_string "Variable known to be defined in an else branch of find: ";
      Display.display_var b tl;
      print_newline ();
      print_string "Elsefind_fact (before renaming): ";
      Facts.display_elsefind elsefind_fact
    end;

  (* decompose def_list into subterms: all *subterms* of def_list must
     be defined before the find so that we can conclude not(t1) from
     the elsefind fact. *)
  let def_list_subterms = ref [] in
  List.iter (Terms.close_def_subterm def_list_subterms) def_list;
  let def_list = !def_list_subterms in

  (* Optimization: if we know that an element br1 is defined before br2 = (b2,tl2) in deflist', 
     we can remove br1. Indeed, assuming that br2 is defined before (b,tl) implies that
     br1 is defined before (b,tl), so that is enough to apply the elsefind fact. 
     This optimization does not seem to affect much the speed of the system. *)
  let rec filter_def_list already_seen = function
      [] -> List.rev already_seen
    | ((b2,tl2)::l) ->
	let before_br2 = 
	  try 
            Terms.subst_def_list b2.args_at_creation tl2 (Facts.def_vars_from_defined None [Terms.binderref_from_binder b2])
	  with Contradiction -> 
	    (* Contradiction may be raised when b2 can in fact not be defined. *)
	    []	
	in
	let already_seen' = Terms.setminus_binderref already_seen before_br2 in
	let l' = Terms.setminus_binderref l before_br2 in
	filter_def_list ((b2,tl2)::already_seen') l'
  in
  let def_list = filter_def_list [] def_list in

  (* transform the elsefind fact such that the variable (b,b.args_at_creation) 
     for the original fact corresponds to our variable (b,tl):
     substitute b.args_at_creation with tl *)
  let b_index = b.args_at_creation in
  let def_list = Terms.subst_def_list b_index tl def_list in
  let t1 = Terms.subst b_index tl t1 in

  if (!Settings.debug_elsefind_facts) then
    begin
      print_string "Elsefind_fact (after renaming): ";
      Facts.display_elsefind (bl,def_list,t1)
    end;

  (* We have [elsefind_fact = (bl,def_list,t1)], which means [forall bl, not (defined(def_list) && t1)].
     We collect in variable [result] the pairs (def_list', t') instances of (def_list, t1) such that
     the elements of [def_list'] are defined at the current program point. (They are in [def_vars].) *)
  let result = ref [] in
  begin
    try 
      match_among_list (final_next3 bl def_list t1 result) simp_facts bl def_vars def_list
    with NoMatch -> ()
  end;
    
  List.iter (fun (def_list',t') ->
      if (!Settings.debug_elsefind_facts) then
        begin
          print_string "Elsefind_fact_try:\n";
          Display.display_term t';
          print_newline ();
          print_string "And the def_list':\n";
          Display.display_list Display.display_term (List.map Terms.term_from_binderref def_list');
          print_newline ()
        end;

      (* If \forall br \in def_list', br is defined strictly before (b,tl), 
	 then it is defined before the find that gives the elsefind_fact, and 
	 so (not t') is true, since the "else" branch of that find has been taken.
         In the other case, we must prove that \forall br \in def_list', 
	 if br is defined after or at (b,tl), t' => Contradiction. *)

    (* Variables defined before (b,tl) *)
    let def_vars_before = 
      try 
        Terms.subst_def_list b_index tl (Facts.def_vars_from_defined None [Terms.binderref_from_binder b])
      with Contradiction -> 
	(* Contradiction may be raised when b can in fact not be defined. *)
	[]
    in
      if (!Settings.debug_elsefind_facts) then
        begin
          print_string "Elsefind_fact_vars_before:\n";
          Display.display_list Display.display_term (List.map Terms.term_from_binderref def_vars_before);
          print_newline ()
        end;
      if (
        List.for_all (fun br ->
          (* Let us suppose that br has been defined after or at (b,tl) *)
          if (!Settings.debug_elsefind_facts) then
            begin
              print_string "Let's assume that ";
	      Display.display_term (Terms.term_from_binderref br);
	      print_string " is defined after or simultaneously ";
	      Display.display_term (Terms.term_from_binderref (b,tl));
              print_newline ()
            end;

	  (* If the variable of br is defined at the definition of b, 
	     remove the variables defined at the same time as (b,tl) and br
	     from def_vars_before. (We are not sure that they are defined before br.) *)
	  let vars_at_b = List.concat (List.map (fun n -> n.binders) b.def) in
	  let def_vars_before = 
	    if List.memq (fst br) vars_at_b then
	      Terms.setminus_binderref def_vars_before (List.map (fun b' -> (b', tl)) vars_at_b)
	    else
	      def_vars_before
	  in

	  (* If br is in def_vars_before, br is defined before (b,tl), so the assumption 
	     that br is defined after (b,tl) never holds. *)
	  (Terms.mem_binderref br def_vars_before) || (
          let order_assumptions = [br,(b,tl)] in
          List.for_all (fun n -> (* for each definition def_node of br *)
            try
                (* Compute variables that are defined after (b,tl):
		   add to the future variables of br the variables defined between the previous input 
		   point and the definition of br and after another definition of (b,_). *)
              let future_binders = add_vars_until_binder_or_node n [b] (above_input_node n) n.future_binders in
	      let future_vars = Terms.subst_def_list (fst br).args_at_creation (snd br) (List.map Terms.binderref_from_binder future_binders) in

	      (* Variables in [def_vars] are known to be defined.
                 If they cannot be defined before [(b,tl)] or a binderref 
		 already in [future_vars], then they
	         are certainly defined after [(b,tl)], so we can add them
	         to [future_vars] *)
	      let future_vars = 
		List.fold_left (fun future_vars br' ->
		  if (not (Terms.may_def_before br' (b,tl) &&
			   List.for_all (Terms.may_def_before br') future_vars)) &&
		     (not (Terms.mem_binderref br' future_vars)) 
		  then
		    br' :: future_vars
		  else
		    future_vars) future_vars def_vars
	      in

              if (!Settings.debug_elsefind_facts) then
                begin
                  print_string "Elsefind_fact_future_vars:\n";
                  Display.display_list Display.display_term (List.map Terms.term_from_binderref future_vars);
                  print_newline ()
                end;

	      (* Elements of future_vars are defined after those of def_vars_before;
	         If they are in def_vars_before, that's a contradiction *)
	      if List.exists (fun future_br -> Terms.mem_binderref future_br def_vars_before) future_vars then
		raise Contradiction;

	      (* Since br is defined after (b,tl), all elements of future_vars are defined after (b,tl).
		 The elements of def_vars_before are defined before (b,tl), so before the elements
		 of future_vars. 
		 Therefore, the elements of def_vars_before are independent of the elements of future_vars
		 that are randomly chosen. *)
              let dep_info = (future_vars, List.map Terms.term_from_binderref def_vars_before) in
     
                if (!Settings.debug_elsefind_facts) then
                  begin
                    print_string "--Args to dependency_collision:\n";
                    print_string "Cur_array=";
                    Display.display_list Display.display_repl_index cur_array;
                    print_string "\nOrder assumptions=";
                    Display.display_list (fun (br,br') -> 
		      print_string "(";
                      Display.display_list Display.display_term (List.map Terms.term_from_binderref [br;br']); 
		      print_string ")"
			) order_assumptions;
                    print_string "\nDepinfo=previous lists";
                    print_string "\nFacts=\n";
                    Facts.display_facts simp_facts;
                    print_string "\nt'=";
                    Display.display_term t';
                    print_string "\n--End of args"; print_newline ();
                    Settings.debug_simplif_add_facts := true;
                  end;
           
	      (* Get additional facts using again elsefind facts.
		 If an elsefind fact (bl, def_list, t1) holds at the
		 definition of b'[tl'] in future_vars, that is,
		 at the definition of b'[tl'], we have
		   forall bl, not (defined(def_list) && t1)
		 and furthermore all elements of def_list are in 
		 def_vars_before, so all elements of def_list are defined
		 at the definition of b[tl], so a fortiori at the
		 definition of b'[tl'], then we have not(t1). *)

              let (subst, facts, _) = simp_facts in
	      let fact_accu = ref (subst@facts) in
	      let elsefind_facts = collect_eff future_vars in
	      List.iter (fun ((b',tl'), (bl, def_list, t1)) ->
		(* The "elsefind" fact (bl, def_list, t1) holds
		   at the definition of b', and I know that b'[tl'] is defined *)

		(* Rename indices b'.args_at_creation -> tl *)
		let def_list = Terms.subst_def_list b'.args_at_creation tl' def_list in
		let t1 = Terms.subst b'.args_at_creation tl' t1 in

                (* We add to [fact_accu] the facts [not t'] where the pairs 
		   (def_list', t') are instances of (def_list, t1) such that
		   the elements of [def_list'] are defined at the definition of b[tl]. 
		   (They are in [def_vars_before].) *)
		begin
		  try 
		    match_among_list (final_next4 bl def_list t1 fact_accu) simp_facts bl def_vars_before def_list
		  with NoMatch -> ()
		end;
		  ) elsefind_facts;

              let (_,_,_) = Facts.simplif_add_list (dependency_collision_order_hyp cur_array order_assumptions dep_info) ([],[],[]) (t'::(!fact_accu)) in
                if (!Settings.debug_elsefind_facts) then
                  begin
                    Settings.debug_simplif_add_facts := false;
                    print_string "Failed to obtain a contradiction.";
                    print_newline ()
                  end;
                false
            with Contradiction -> 
              if (!Settings.debug_elsefind_facts) then
                begin
                  Settings.debug_simplif_add_facts := false;
                  print_string "Obtained a contradiction.";
                  print_newline ()
                end;
              true
                ) (fst br).def
	    )
            ) def_list'; 
      )
      then
        begin
          (* The term (not t') is true, add it *)
          let t = Terms.make_not t' in
          term_accu := t :: (!term_accu);
          if (!Settings.debug_elsefind_facts) then
	    begin
	      print_string "Found a usable term: ";
	      Display.display_term t;
	      print_newline ()
	    end
        end
      else
        begin
          if (!Settings.debug_elsefind_facts) then
            begin
              print_string "Found no usable terms.";
              print_newline ()
            end
	end
	  ) (!result)


let get_facts_of_elsefind_facts g cur_array simp_facts def_vars =
  if (!Settings.debug_elsefind_facts) then
    begin
      print_string "__________________\n";
      print_string "Elsefind begin\n";
      print_newline ()
    end; 
(*  print_string "Defined variables original:\n";
  List.iter (fun (b,l) -> Display.display_var b l; print_newline()) def_vars; *)
  let def_vars_tmp = ref [] in
  List.iter (fun (b,l) ->
    let br' = (b, List.map (Terms.try_no_var simp_facts) l) in
    Terms.add_binderref br' def_vars_tmp) def_vars;
  let def_vars = !def_vars_tmp in
(*  print_string "Defined variables simplified:\n";
  List.iter (fun (b,l) -> Display.display_var b l; print_newline()) def_vars; *)
  let term_accu = ref [] in
  let effl = collect_eff def_vars in
  List.iter (fun (br, eff) -> get_fact_of_elsefind_fact term_accu g cur_array def_vars simp_facts br eff) effl;
  if (!Settings.debug_elsefind_facts) then
    begin
      print_string "__________________\n";
      print_string "Elsefind summary: these terms are true:\n";
      Display.display_list Display.display_term (!term_accu);
      print_newline ()
    end;
  (!term_accu)


(***** Filter out the indices that are unique knowing other indices *****
       (useful for reducing the probabilities in the crypto transformation) 
       Terms.build_def_process must have been called so that t.t_facts has 
       been filled. For use from cryptotransf.ml.
*)

type compat_info_elem = term * term list * 
      repl_index list(* all indices *) * 
      repl_index list(* initial indices *) * 
      repl_index list(* used indices *) * 
      repl_index list(* really used indices *)

(* true_facts0 must not contain if/let/find/new. 
   if the initial indices contain "noninteractive" indices, we try
   to eliminate them, even by adding "interactive" indices, as follows: 
   start from a list of indices that consists of
   (1) the "noninteractive" indices in the initial useful indices
   (2) the "interactive" indices that occur in all_indices but not in the 
      initial useful indices
   (3) the "interactive" indices that occur in the initial indices
   and try to eliminate the indices in order. At each step, we check that all
   indices in the initial useful indices are uniquely determined. 
   *)

let filter_indices t true_facts0 all_indices used_indices =
  let proba_state = Proba.get_current_state() in
  (* Collect all facts that are known to be true *)
  let true_facts = 
    try
      true_facts0 @ (Facts.get_facts_at t.t_facts)
    with Contradiction ->
      [Terms.make_false()]
  in
  let used_indices' = List.map Terms.repl_index_from_term used_indices in
  (* Try to reduce the list of used indices. 
     The initial list of indices is a reordering of the list of all indices.
     We start with the larger indices (to eliminate them first) and among
     the indices of the same size, with those that are not in used_indices
     (also to eliminate them first).
     The goal is to try to remove large indices
     of used_indices, perhaps at the cost of adding more
     smaller indices of all_indices. *)
  let initial_indices =
      (* Sort used_indices and all_indices in decreasing size *)
      let used_indices_sort = List.sort greater_size used_indices' in
      let all_indices_sort = List.sort greater_size all_indices in
      (* Remove elements of all_indices that are in used_indices *)
      let all_indices_sort_minus_used_indices = List.filter (fun b -> not (List.memq b used_indices_sort)) all_indices_sort in
      (* Build a list by merging indices from all_indices and used_indices.
	 When indices are of the same size, we put elements of all_indices first,
	 so that they will be eliminated, except if they are now necessary
	 because they replace some larger index eliminated before. *)
      List.merge greater_size all_indices_sort_minus_used_indices used_indices_sort 
  in
  (* Try to remove useless indices using true_facts *)
  let really_used_indices = filter_indices_coll true_facts used_indices' initial_indices in
  if really_used_indices == initial_indices then
    begin
      (* I removed no index, I can just leave things as they were *)
      Proba.restore_state proba_state;
      (used_indices, (t, true_facts, all_indices, initial_indices, used_indices', used_indices'))
    end
  else
    (List.map Terms.term_from_repl_index really_used_indices, 
     (t, true_facts, all_indices, initial_indices, used_indices', really_used_indices))

(***** Test if two expressions can be evaluated with the same value of *****
       certain indices. 
       (useful for reducing the probabilities in the crypto transformation) 
       For use from cryptotransf.ml.
*)

(* TO DO Also exploit defined variables using CompatibleDefs2.check_compatible2_deflist *)

let rec find_same_type b = function
    [] -> raise Not_found 
  | b''::r ->
      if b''.ri_type == b.ri_type then
	(* relate b to b'' *)
	(b'', r)
      else
	let (bim, rest_r) = find_same_type b r in
	(bim, b''::rest_r)

let is_compatible_indices 
    (t1, true_facts1, all_indices1, _, _, really_used_indices1) 
    (t2, true_facts2, all_indices2, _, _, really_used_indices2) =
  (*
  print_string "Simplify.is_compatible_indices ";
  Display.display_term t1;
  print_string " with ";
  Display.display_term t2;
  *)
  let proba_state = Proba.get_current_state() in
    (* Find a relation between really_used_indices1 and really_used_indices2 that
       respect types. *)
  if (!current_bound_ri) != [] then
    Parsing_helper.internal_error "current_bound_ri should be cleaned up (simplify, filter_indices)";
  let really_used_indices1' = ref really_used_indices1 in
  List.iter (fun b -> 
    if List.memq b really_used_indices2 then
      try
	let (b', rest_really_used_indices1) = find_same_type b (!really_used_indices1') in
	really_used_indices1' := rest_really_used_indices1;
	ri_link b (TLink (Terms.term_from_repl_index b'))
      with Not_found -> 
	let b' = new_repl_index b in
	ri_link b (TLink (Terms.term_from_repl_index b'))
    else
      let b' = new_repl_index b in
      ri_link b (TLink (Terms.term_from_repl_index b'))
	) all_indices2;
  let true_facts2' = List.map (Terms.copy_term Terms.Links_RI) true_facts2 in
  ri_cleanup();
  try
    ignore (Terms.auto_cleanup (fun () -> 
      Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) (true_facts1 @ true_facts2')));
    (* The terms t1 and t2 are compatible: they may occur for the same indices *)
    (* print_string " true\n";  *)
    Proba.restore_state proba_state;
    true
  with Contradiction ->
    (* The terms t1 and t2 are not compatible *)
    (* print_string " false\n"; *)
    false


(* Test if two terms represent in fact calls to the same oracle
   (and so should be counted only once when computing probabilities) 
   For use from cryptotransf.ml.
*)

(*
TO DO I should use a form of antiunification: when t1 and t2
are not exactly equal, I can replace subterms at the same
occurrence of t1 and t2 with the same fresh variable.
When I see the same pair of subterms in the computation of
common facts, I reuse the same variable.
I must then check that the common facts imply that this variable has
a unique value for each value of the really_used_indices.

Remark: since the desired result of filter_indices is known,
I could be faster and avoid trying to remove indices in
really_used_indices.
*)

(* Oracle call t1 means: for all indices in t1 and true_facts1 such that true_facts1 holds, call t1.
   Oracle call t2 means: for all indices in t2 and true_facts2 such that true_facts2 holds, call t2.
There is a substitution sigma such that
 * t2 = sigma t1
 * There is a subset common_facts of true_facts1 suchthat
   true_facts2 contains at least sigma common_facts 
 * The same indices can be removed using common_facts as
   using true_facts1, so that the used indices at t1 with common_facts
   are still really_used_indices1.
Then we replace both calls with
  for all indices in t1 and common_facts such that common_facts holds, call t1
This is more general than t1 and t2 and yields the same cardinal as t1. *)

let match_oracle_call 
    (t1, true_facts1, all_indices1, initial_indices1, used_indices1, really_used_indices1) 
    (t2, true_facts2, all_indices2, initial_indices2, used_indices2, really_used_indices2) =
  (*
  print_string "Simplify.same_oracle_call ";
  Display.display_term t1;
  print_string " with ";
  Display.display_term t2;
    *)
  Terms.auto_cleanup(fun () ->
    if eq_terms3 t1 t2 then
      let common_facts = List.filter (fun f1 -> List.exists (fun f2 -> eq_terms3 f1 f2) true_facts2) true_facts1 in
      ri_cleanup();
      let proba_state = Proba.get_current_state() in
      (* Check that we can remove the same indices using common_facts as with all facts *)
      let really_used_indices1' = filter_indices_coll common_facts used_indices1 initial_indices1 in
      let r1 = Terms.equal_lists (==) really_used_indices1 really_used_indices1' in
      if r1 then
	begin
	  (*
	  print_string "Simplify.same_oracle_call ";
	  Display.display_term t1;
	  print_string " with ";
	  Display.display_term t2;
	  print_string " succeeds\n";
	  print_string "Common facts:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) common_facts;
	  *)
	  Some (t1, common_facts, all_indices1, initial_indices1, used_indices1, really_used_indices1)
	end
      else
	begin
	  (*
	  print_string "Simplify.same_oracle_call ";
	  Display.display_term t1;
	  print_string " with ";
	  Display.display_term t2;
	  print_string " fails\n";
	  print_string "True facts 1:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) true_facts1;
	  print_string "True facts 2:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) true_facts2;
	  print_string "Common facts:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) common_facts;
	  print_string "used_indices_map1\n";
	  Display.display_list (fun (t,t') ->
	    print_string "("; Display.display_term t; print_string ", "; Display.display_term t'; print_string ")") used_indices_map1;
	  print_newline();
	  print_string "used_indices_map1'\n";
	  Display.display_list (fun (t,t') ->
	    print_string "("; Display.display_term t; print_string ", "; Display.display_term t'; print_string ")") used_indices_map1';
	  print_newline();
	  print_string "used_indices1\n";
	  Display.display_list Display.display_term used_indices1;
	  print_newline();*)
	  Proba.restore_state proba_state;
	  None
	end
    else
      begin
	(*
	  print_string "Simplify.same_oracle_call ";
	  Display.display_term t1;
	  print_string " with ";
	  Display.display_term t2;
	  print_string " fails\n";*)
	None
      end
    )

let same_oracle_call call1 call2 =
  match match_oracle_call call1 call2 with
    None -> match_oracle_call call2 call1
  | r -> r
