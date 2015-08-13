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

(* Test equality of processes modulo renaming of variables.
   Used to simplify tests and find: when all branches are equal,
   the test/find can be removed.
   There is room for more general equivalences between processes,
   but this is already a first step.
 *)

type 'a eqtester

val equal_oprocess : process eqtester
val equal_find_cond : term eqtester

val equal : 'a eqtester -> simp_facts -> 'a -> 'a -> bool
val can_merge_all_branches : 'a eqtester ->
    fact_info -> simp_facts -> 'a findbranch list -> 'a -> bool 
val can_merge_one_branch : 'a eqtester ->
    fact_info -> simp_facts -> 'a findbranch -> 'a -> bool 

(* [merge_arrays bll mode g] merges arrays 
   contained in [bll] in game [g]. [bll] is a list of list of variables, say
   bll = [[b11, ..., b1n],[b21, ..., b2n], ..., [bk1, ..., bkn]]
   Each list [bi1,...,bin] corresponds to variables to merge together; they
   are merged to bi1. See comments in mergebranches.ml for more details.

   The terms and processes in the input game must be physically
   distinct, since [Terms.build_def_process] is called. The terms and
   processes in the returned game are *not* guaranteed to be physically
   distinct. They are made distinct later in instruct.ml by calling
   [Terms.move_occ_process].
 *)

val merge_arrays : (binder * Parsing_helper.extent) list list -> merge_mode -> game_transformer

(* [merge_branches g] merges branches of find
   as much as possible in game [g].

   The terms and processes in the input game must be physically
   distinct, since [Terms.build_def_process] is called. *)

val merge_branches : game_transformer
