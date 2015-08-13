#!/bin/sh

CRYPTOKIT="-I ../cryptokit -I +cryptokit"

cd ../.. 
echo Proving the protocol...
./cryptoverif implementation/nspk/nspk3tbl.ocv > implementation/nspk/nspk3tbl.out
egrep '(RESULT|All)' implementation/nspk/nspk3tbl.out | grep -v "RESULT time"
echo Generating implementation...
./cryptoverif -impl -o implementation/nspk implementation/nspk/nspk3tbl.ocv 
cd implementation/nspk

rm idA idB idS pkA pkB pkS skA skB skS keytbl t tl

ocamlopt $CRYPTOKIT -I .. -o Skeygen unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_Keygen.mli ONS_Keygen.ml Skeygen.ml
ocamlopt $CRYPTOKIT -I .. -o Akeygen unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_AGenKey.mli ONS_AGenKey.ml Akeygen.ml
ocamlopt $CRYPTOKIT -I .. -o Bkeygen unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_BGenKey.mli ONS_BGenKey.ml Bkeygen.ml
ocamlopt $CRYPTOKIT -I .. -o A unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_A.mli ONS_A.ml A.ml
ocamlopt $CRYPTOKIT -I .. -o B unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_B.mli ONS_B.ml B.ml
ocamlopt $CRYPTOKIT -I .. -o S unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_S.mli ONS_S.ml S.ml

ocamlopt $CRYPTOKIT -I .. -o test unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_Keygen.mli ONS_Keygen.ml ONS_B.mli ONS_B.ml ONS_AGenKey.mli ONS_AGenKey.ml ONS_BGenKey.mli ONS_BGenKey.ml ONS_A.mli ONS_A.ml ONS_S.mli ONS_S.ml test.ml
