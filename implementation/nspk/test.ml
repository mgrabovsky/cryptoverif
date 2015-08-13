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


(*protocol test *)

(*init S key*)
print_string "Ostart...";print_newline ();
let ostart=ONS_Keygen.init () in
let (_,pkS) = ostart () in

(*init A key*)
print_string "OAGK...";print_newline ();
let oagk = ONS_AGenKey.init () in
let (_,pkA) = oagk () in

(*init B key*)
print_string "OBGK...";print_newline ();
let obgk = ONS_BGenKey.init () in
let (_,pkB) = obgk () in
let b=Base.input_string_from_file "idB" in

(*A 1*)
print_string "OA1...";print_newline ();
let oa1 = ONS_A.init () in
let (oa3, hA,hB) = oa1 b in
print_string (hA^","^hB);print_newline ();

(*S 2*)
print_string "OS13";print_newline ();
let os13 = ONS_S.init () in
let (_,rk,h2,s) = os13 (hA, hB) in

(*A 3*)
print_string "OA3";print_newline ();
let (oa5,c) = oa3 (rk, h2, s) in

(*B 4*)
print_string "OB7";print_newline ();
let ob7 = ONS_B.init () in
let (ob9,hB',hA') = ob7 c in

(*S 5*)
print_string "OS13'";print_newline ();
let os13' = ONS_S.init () in
let (_,rk',h2',s') = os13' (hB', hA') in

(*B 6*)
print_string "OB9";print_newline ();
let (ob11, c') = ob9 (rk', h2', s') in

(*A 7*)
print_string "OA5";print_newline ();
let (_,m) = oa5 c' in

(*B 8*)
print_string "OB11";print_newline ();
let _ = ob11 m in
  ()


