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
(* Types module declares types of the abstract syntax
   tree and of sets of messages.
   There are recursive dependencies between these types,
   that is why they are included in the same module
*)

type ident = string * Parsing_helper.extent

(* integer parameter *)

type param = { pname : string;
	       psize : int }

(* probability *)

type proba = { prname : string }

(* channel *)

type channel = { cname : string }

(* types *)

type typet = { tname : string;
	       tcat : ttcat;
	       toptions : int;
	       tsize : int; 
	       (* The next fields are used for generating OCaml implementations *)
               mutable timplsize : int option; 
                 (* Number of bits of bitstrings of this type, when they have a fixed length *) 
               mutable tpredicate : string option;
	         (* Name of the OCaml function that tests whether an OCaml element belongs to
		    this type. *)
               mutable timplname : string option;
	         (* Name of the OCaml type that corresponds to this type *)
               mutable tserial : (string * string) option;
	         (* Name of the OCaml serialization and deserialization functions for this type *)
               mutable trandom : string option 
		 (* Name of the OCaml random element generation for this type *)
	     }

and ttcat = 
    BitString
  | Interv of param


type table = { tblname : string;
               tbltype : typet list;
	         (* Type of the elements of the table *)
	       (* The next field is used for generating OCaml implementations *)
               mutable tblfile : string option
		 (* Name of the file that contains this table *)
	     }


type find_info =
    Nothing
  | Unique

(* terms *)

type binder = { sname : string;
                vname : int;
		   (* The name of a variable consists of two elements:
		      sname is a string, vname is an integer, the full name
		      of the variable is sname_vname. 
		      When I want to rename a variable, I keep its sname
		      and choose a fresh integer vname. *)
		btype : typet; 
		   (* The type of the variable *)
		args_at_creation : repl_index list;
		   (* The replication indices coming from replications and find
		      above the definition of this variable. 
		      These are the indices at the definition of the variable,
		      and also the indices used implicitly when the variable
		      is used without explicit indices. *)
		mutable def : def_node list;
		   (* Pointer to the nodes at which this variable is defined. 
		      Set by Terms.build_def_process. *)
		mutable link : linktype;
		   (* Link of the variable to a term. 
		      This is used for implementing substitutions:
		      1. One sets the links to the desired images of the variables.
		      2. Then one copies terms, replacing links with their value.
		      3. Finally one cleans up the links. *)

		   (* The next fields count_def...count_exclude_array_ref
		      mainly deal with array references. 
                      They are set by Terms.array_ref_process *)
		mutable count_def : int;
		   (* Number of definitions of the variable *)
	        mutable root_def_array_ref : bool;
		   (* True when the variable has an array
		      reference at the root of a defined condition:
		         defined(b[l]) with l <> b.args_at_creation
		      or b not in scope. *)
	        mutable root_def_std_ref : bool;
		   (* True when the variable has a standard reference
		      at the root of a defined condition:
			 defined(b[b.args_at_creation])
		      with b in scope. Such defined conditions can be removed. *)
	        mutable array_ref : bool;
		   (* True when the variable has an array reference
		      b[l] with l <> b.args_at_creation
		      or b not in scope, not at the root of a defined condition *)
                mutable std_ref : bool;
		   (* True when the variable has a standard reference
		      b[b.args_at_creation] with b in scope, not at
                      the root of a defined condition. *)
		mutable count_array_ref : int;
		   (* Number of array references to this variable
                      (including those at the root of defined conditions) *)
		mutable count_exclude_array_ref : int;
		   (* When we want to know if a variable has array references
		      outside certain terms, we first count the total
		      number of array references (using Terms.array_ref_process),
		      then exclude the array references in the considered 
		      terms, by counting them in the field 
		      count_exclude_array_ref using Terms.exclude_array_ref_term. *)
	        mutable priority : int 
		   (* This integer is used to improve the orientation
		      of equations, see Facts.orient *)
	      }

and binderref = binder * term list

(* Definition graph *)
and def_node = { above_node : def_node;
		 binders : binder list; (* The variables defined at this node *)
		 true_facts_at_def : term list; 
                    (* The facts that are guaranteed to be true at this node *)
		 def_vars_at_def : binderref list; 
                    (* The variables that are guaranteed to be defined at 
		       this node, due to defined conditions above this node *)
		 elsefind_facts_at_def : elsefind_fact list;
		    (* The elsefind_facts that are guaranteed to be true just 
		       before this node. (If this node defines b, and the
                       elsefind_fact is forall bl, not (defined(b[...]) && t),
                       the elsefind_fact may no longer hold after the definition
                       of b, but it is still present in elsefind_facts_at_def.) 
		       *)
		 mutable future_binders : binder list;
		    (* The variables that are guaranteed to be defined
		       before we reach the end of the current input...output block.
		       They come from let definitions and restrictions after this
		       node. *)
		 mutable future_true_facts : term list;
		    (* The facts that are guaranteed to be defined 
		       before we reach the end of the current input...output block.
		       They come from let definitions and events after this node. *)
	         definition : program_point;
		    (* Pointer to the process or term that contains the variable definition *)
		 definition_success : program_point
		   (* Pointer to the process or term that is executed just after the variable is defined *)
	       }

and program_point = 
    DProcess of process
  | DInputProcess of inputprocess
  | DTerm of term
  | DFunRestr
  | DFunArgs
  | DGenVar
  | DNone

and linktype = 
    NoLink
  | TLink of term

and funcats = 
    Std
  | Tuple 
  | Equal
  | LetEqual (* Special equality symbol for let assignments *)
  | Diff
  | ForAllDiff (* Special symbol meaning "for all variables named ?x_..., t1 <> t2" *)
  | Or
  | And
  | Event (* Function symbols for events *)
  | LetFunTerm of binder list * term

and impl_name =
    Func of string
  | Const of string
  | No_impl

and funsymb = { f_name : string;
		f_type : typet list * typet; (* argument and result types *)
                f_cat : funcats;
	    	f_options : int; (* options *)
		mutable f_statements : collision list;
		mutable f_collisions : collision list;
		mutable f_eq_theories : eq_th; (* equational theories for this function symbol *)
                mutable f_impl : impl_name; (* implementation name *)
                mutable f_impl_inv : string option; (* implementation of inverse if applicable *)
              }

and eq_th =
    NoEq
  | Commut 
  | Assoc 
  | AssocCommut 
  | AssocN of funsymb(*associative function*) * funsymb(*neutral*)
  | AssocCommutN of funsymb(*AC function*) * funsymb(*neutral*)
  | Group of funsymb(*mult*) * funsymb(*inverse*) * funsymb(*neutral*)
  | CommutGroup of funsymb(*mult*) * funsymb(*inverse*) * funsymb(*neutral*)
  | ACUN of funsymb(*xor*) * funsymb(*neutral*)

(* Replication index *)
and repl_index = { ri_sname : string;
                   ri_vname : int;
		     (* The name of the replication index consists of two elements:
			ri_sname is a string, ri_vname is an integer, the full name
			of the replication index is (ri_sname)_(ri_vname). 
			This is similar to the name of variables. *) 
		   ri_type : typet; 
		     (* Type of the replication index.
			Must be an interval *)
		   mutable ri_link : linktype
		     (* Link of the replication index to a term.
			This is used for implementating substitutions. *)
		 }

and term_desc = 
    Var of binder * term list (* array access *)
  | ReplIndex of repl_index (* replication index *)
  | FunApp of funsymb * term list
  | TestE of term * term * term
  | FindE of term findbranch list * term * find_info
  | LetE of pattern * term * term * term option
  | ResE of binder * term
  | EventAbortE of funsymb

and 'a findbranch = (binder(*the variable defined when the find succeeds*) * repl_index(*the corresponding replication index used for searching in the arrays*)) list * binderref list(*guaranteed defined array references*) * term(*condition*) * 'a(*then branch*)

and term = { t_desc : term_desc;
	     t_type : typet;
	     t_occ : int;
	        (* Occurrence of the term *)
	     t_max_occ : int;
	        (* Maximum occurrence of any subterm of the considered term.
		   [Terms.move_occ_term] guarantees that the occurrences of the subterms
		   of the considered term form exactly the interval [t_occ,t_max_occ].
		   When [t_max_occ] cannot be set to satisfy this constraint,
		   it is set to 0. *)
	     t_loc : Parsing_helper.extent;
	     mutable t_incompatible : int Occ_map.occ_map;
	        (* Incompatible program points:
		   if [(pp -> n) \in t.t_incompatible] and 
                   the common suffix of [l] and [l'] has length at least [n], then
		   [t] with indices [l] and [pp] with indices [l'] cannot be both executed.
		   Program points are represented by their occurrence. *)
	     mutable t_facts : fact_info }

and fact_info = (term list * binderref list * def_node) option
      (* Some(true_facts, def_vars, def_node):
	 true_facts = the facts that are true at the current program point
	 def_vars = the variables whose definition is guaranteed because
	    of defined conditions above the current program point
	 def_node = the node immediately above the current program point *)

and elsefind_fact = repl_index list * binderref list * term
      (* The elsefind_fact (bl, def_list, t) means 
	 forall bl, not(defined(def_list) && t) 
	 It is generated in the "else" branch of a 
	 find bl suchthat defined(def_list) && t. *)

(* Processes *)

and pattern = 
    PatVar of binder
  | PatTuple of funsymb * pattern list
  | PatEqual of term

and inputprocess_desc = 
    Nil
  | Par of inputprocess * inputprocess
  | Repl of repl_index * inputprocess
  | Input of (channel * term list) * pattern * process

and inputprocess =
    { i_desc : inputprocess_desc;
      i_occ : int;
      i_max_occ : int;
      mutable i_incompatible : int Occ_map.occ_map; (* similar to t_incompatible *)
      mutable i_facts : fact_info }

and process_desc =  
    Yield
  | EventAbort of funsymb
  | Restr of binder * process 
  | Test of term * process * process
  | Find of process findbranch list * process * find_info
  | Output of (channel * term list) * term * inputprocess
  | Let of pattern * term * process * process
  | EventP of term * process
  | Insert of table * term list * process
  | Get of table * pattern list * term option * process * process

and process =
    { p_desc : process_desc;
      p_occ : int;
      p_max_occ : int;
      mutable p_incompatible : int Occ_map.occ_map; (* similar to t_incompatible *)
      mutable p_facts : fact_info }

(* Equivalences *)

and action =
    AFunApp of funsymb         (* Application of f *)
  | APatFunApp of funsymb      (* Pattern matching with f *)
  | AReplIndex                 (* Reading a replication index *)
  | AArrayAccess of int        (* Array access with n indexes *)
  | ANew of typet              (* Random number generation of type t *)
  | ANewChannel                (* Create a private channel *)
  | AIf                        (* Test *)
  | AFind of int               (* Find: one choice with n indexes to choose *)
  | AOut of typet list * typet (* Output with channel indexes of types tl and output bitstring of type t *)
  | AIn of int                 (* Record input with n channel indexes in input list *)

and mode =
    ExistEquiv | AllEquiv

and options =
    StdOpt | UsefulChange

and restropt =
    NoOpt | Unchanged | DontKnow

and name_to_discharge_t = (binder * restropt ref) list
    
and fungroup =
    ReplRestr of repl_index(*replication*) * (binder * restropt) list(*restrictions*) * fungroup list
  | Fun of channel * binder list(*inputs*) * term * (int(*priority*) * options)

and eqmember = 
    (fungroup * mode) list

and eqopt =
    StdEqopt | ManualEqopt | PrioEqopt of int

and eqopt2 =
    Decisional | Computational

and eqname = 
    CstName of ident
  | ParName of ident * ident
  | NoName


and game = 
    { mutable proc : inputprocess;
      mutable game_number : int;
      mutable current_queries : ((query * game) * proof_t ref * proof_t) list
	(* [current_queries] contains, for each query:
	   [(query, game), proof_ref, proof] where
	   the query [query] should be proved in game [game],
	   [proof = None] when it is not proved yet;
	   [proof = Some(proba, state)] when it is proved up to probability [proba]
	   using the sequence of games [state].
	   However, the probability [proba] may depend on the probability of events
	   introduced during the proof. 
	   [proof_ref] is set to [proof] when the probability of all these events
	   has been bounded. Otherwise, [!proof_ref = None]. *)
    }

and proof_t = (setf list * state) option

and probaf = 
    Proba of proba * probaf list
  | Count of param
  | OCount of channel
  | Add of probaf * probaf
  | Mul of probaf * probaf
  | Cst of float
  | Zero
  | Sub of probaf * probaf
  | Div of probaf * probaf
  | Max of probaf list
  | Card of typet
  | EpsFind (* The distance between the uniform distribution and the one generated by Find when
	       several choices are possible. *)
  | EpsRand of typet (* For bounded types t, the distance between the uniform distribution and the
                        distribution generated by "new x:t" *)
  | PColl2Rand of typet (* Probability of collision between two independent random elements chosen 
			   according to the standard distribution for type t. 
			   This is \sum_{x \in t} P(x)^2, which is at most PColl1Rand(t). *)
  | PColl1Rand of typet (* Probability of collision between one random element chosen according to the standard
			   distribution for type t, and an element of type t that does not depend on it.
			   This is also the maximum probability of choosing any given element of t in the
			   standard distribution for that type.  *)
  | AttTime (* Time of the attacker *)
  | Time of game * probaf (* Time i = runtime of game number i *)
  | ActTime of action * probaf list 
  | Maxlength of game * term
  | TypeMaxlength of typet
  | Length of funsymb * probaf list

(* An element of type [setf list] represents a probability
   computed as the sum of the probabilities [proba] 
   of all elements [SetProba proba] of the list, plus
   the probability of the disjunction of all events
   recorded by elements [SetEvent ...] of the list. *)

and setf =
    SetProba of probaf
  | SetEvent of funsymb * game * proof_t ref

and equiv = eqname * eqmember * eqmember * setf list * eqopt * eqopt2

and def_check = term list

and equiv_nm = equiv * (binder * binder * def_check) list 
        (* equivalence with name mapping *)

(* Logical statements *)

and statement = binder list * term

(* Collision statements *)

and collision = binder list(*restrictions*) * binder list(*forall*) *
      term * probaf * term

(* Queries *)

and qterm =
    QEvent of bool(*true when injective*) * term
  | QTerm of term
  | QAnd of qterm * qterm
  | QOr of qterm * qterm

and query = 
    QSecret1 of binder
  | QSecret of binder
  | QEventQ of (bool(*true when injective*) * term) list * qterm
  | AbsentQuery
  
(* Instructions for modifying games *)

(* For removal of assignments *)
and rem_set =
    All
  | OneBinder of binder
  | FindCond
  | Minimal

and move_set =
    MAll
  | MNoArrayRef
  | MLet
  | MNew
  | MNewNoArrayRef
  | MOneBinder of binder

and merge_mode =
    MNoBranchVar
  | MCreateBranchVar
  | MCreateBranchVarAtProc of process list * repl_index list
  | MCreateBranchVarAtTerm of term list * repl_index list

(* User info for cryptographic transformation *)

and var_mapping = (binder(*variable in game*) * binder(*variable in equivalence*)) list * 
      binder(*variable in game, when the corresponding variable in equivalence is not known*) list * bool
    (* bool is true when the list ends with "."
       no other variable should be added by the transformation in this case *)
and term_mapping = (int(*occurrence in game*) * term(*oracle in equivalence*)) list * bool

and crypto_transf_user_info =
    VarList of binder list * bool (* bool is true when the list ends with "."
				    no other variable should be added by the transformation in this case *)
  | Detailed of var_mapping option * term_mapping option
	
and instruct =
    ExpandIfFindGetInsert
  | Simplify of string list(*occurrences, variables, or types for collision elimination of password types*)
  | GlobalDepAnal of binder * string list (* same as for Simplify *)
  | RemoveAssign of rem_set
  | SArenaming of binder
  | MoveNewLet of move_set
  | CryptoTransf of equiv_nm * crypto_transf_user_info
  | InsertEvent of string(*event name*) * int(*occurrence of insertion*) 
  | InsertInstruct of string(*instruction*) * Parsing_helper.extent * int (*occurrence of insertion*) * Parsing_helper.extent
  | ReplaceTerm of string(*term*) * Parsing_helper.extent * int (*occurrence of replacement*) * Parsing_helper.extent
  | MergeArrays of (binder * Parsing_helper.extent) list list * merge_mode
  | MergeBranches
  | Proof of ((query * game) * setf list) list

and ins_updater = (instruct -> instruct list) option

and to_do_t = (instruct list * int * name_to_discharge_t) list

and simplify_internal_info_t = 
    (binder * binder) list * (term * term * probaf * (binder * term) list) list

(* Detailed game transformations. Used to record what transformations 
   have been done. *)

and pat_simp_type = 
    DEqTest
  | DExpandTuple
  | DImpossibleTuple

and simplify_ins =
    SReplaceTerm of term * term
  | STestTrue of process
  | STestFalse of process
  | STestMerge of process
  | STestOr of process
  | STestETrue of term
  | STestEFalse of term
  | STestEMerge of term
  | STestEOr of term
  | SFindBranchRemoved of process * process findbranch
  | SFindSingleBranch of process * process findbranch
  | SFindRemoved of process 
  | SFindElseRemoved of process
  | SFindBranchMerge of process * process findbranch list
  | SFindDeflist of process * binderref list * binderref list
  | SFindinFindCondition of process * term
  | SFindinFindBranch of process * process
  | SFindtoTest of process
  | SFindIndexKnown of process * process findbranch * (binder * term) list
  | SFindEBranchRemoved of term * term findbranch
  | SFindESingleBranch of term * term findbranch
  | SFindERemoved of term
  | SFindEElseRemoved of term
  | SFindEBranchMerge of term * term findbranch list
  | SFindEDeflist of term * binderref list * binderref list
  | SFindinFindECondition of term * term
  | SFindinFindEBranch of term * term
  | SFindEtoTestE of term
  | SFindEIndexKnown of term * term findbranch * (binder * term) list
  | SLetElseRemoved of process
  | SLetRemoved of process
  | SLetSimplifyPattern of process * pattern * pat_simp_type
  | SLetEElseRemoved of term
  | SLetERemoved of term
  | SLetESimplifyPattern of term * pattern * pat_simp_type
  | SResRemoved of process
  | SResToAssign of process
  | SResERemoved of term
  | SResEToAssign of term

and def_change =
    DRemoveDef
  | DKeepDefPoint
  | DKeepDef

and usage_change =
    DRemoveAll
  | DRemoveNonArray

and detailed_instruct =
    DExpandGetInsert of table
  | DExpandIfFind
  | DSimplify of simplify_ins list
  | DGlobalDepAnal of binder * string list
  | DLetSimplifyPattern of process * pattern * pat_simp_type
  | DLetESimplifyPattern of term * pattern * pat_simp_type
  | DRemoveAssign of binder * def_change * usage_change
  | DSArenaming of binder * binder list
  | DMoveNew of binder
  | DMoveLet of binder
  | DCryptoTransf of equiv_nm * crypto_transf_user_info
  | DInsertEvent of funsymb(*event name*) * int(*occurrence of insertion*) 
  | DInsertInstruct of string * int (*occurrence of insertion*)
  | DReplaceTerm of term * term * int (*occurrence of replacement*)
  | DMergeArrays of (binder * Parsing_helper.extent) list list * merge_mode
  | DMergeBranches of process * process list
  | DMergeBranchesE of term * term list

(* The type of game transformations: they take as input a game
and return a triple (transformed game, probability difference,
detailed description of the transformation).
Game transformations also set Transform.changed when they actually
modify the game, and add advised instructions in Transform.advise. *)

and game_transformer = game -> game * setf list * detailed_instruct list

(* State. Used to remember a sequence of game modifications *)

and state =
    { game : game;
      prev_state : (instruct * setf list * detailed_instruct list * state) option }

(* Result of a cryptographic transformation *)
type failure_reason =
    Term of term
  | UntransformableTerm of term
  | RefWithIndicesWithoutMatchingStandardRef of binderref * binderref
  | RefWithIndicesWithIncompatibleStandardRef of binderref * binderref * int
  | IncompatibleRefsWithIndices of binderref * binderref * binderref * binderref * int
  | NoChange
  | NoChangeName of binder
  | NoUsefulChange
  | NameNeededInStopMode


type trans_res =
    TSuccess of setf list * detailed_instruct list * game
  | TFailure of (equiv_nm * crypto_transf_user_info * instruct list) list * ((binder * binder) list * failure_reason) list

type simp_facts = term list * term list * elsefind_fact list
type dep_anal = simp_facts -> term -> term -> term option

exception NoMatch
exception Contradiction

(* For the generation of implementations
   type for a program : name, options, process *)

type impl_opt = Read of binder * string | Write of binder * string 

type impl_process = string * impl_opt list * inputprocess

