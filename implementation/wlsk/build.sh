#!/bin/sh

CRYPTOKIT="-I ../cryptokit -I +cryptokit"

cd ../.. 
echo Proving the protocol...
./cryptoverif implementation/wlsk/woolamskcorr_tbl.cv > implementation/wlsk/woolamskcorr_tbl.out
egrep '(RESULT|All)' implementation/wlsk/woolamskcorr_tbl.out | grep -v "RESULT time"
echo Generating implementation...
./cryptoverif -impl -o implementation/wlsk implementation/wlsk/woolamskcorr_tbl.cv
cd implementation/wlsk

rm keytbl wlsk_enc_key wlsk_mac_key wlsk_id

ocamlopt $CRYPTOKIT -I .. -o keygen unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml WLSK_keygen.mli WLSK_keygen.ml keygen.ml
ocamlopt $CRYPTOKIT -I .. -o server unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml WLSK_S.mli WLSK_S.ml server.ml
ocamlopt $CRYPTOKIT -I .. -o init unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml WLSK_Init.mli WLSK_Init.ml init.ml
ocamlopt $CRYPTOKIT -I .. -o resp unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml WLSK_Resp.mli WLSK_Resp.ml resp.ml

ocamlopt $CRYPTOKIT -I .. -o test_wlsk unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml WLSK_Init.mli WLSK_Init.ml WLSK_Resp.mli WLSK_Resp.ml WLSK_S.mli WLSK_S.ml WLSK_keygen.mli WLSK_keygen.ml test_wlsk.ml
