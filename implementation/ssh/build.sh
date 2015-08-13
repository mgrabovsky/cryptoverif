#!/bin/sh

CRYPTOKIT="-I ../cryptokit -I +cryptokit"

cd ../.. 
echo Proving the protocol...
echo First, proving authentication
./cryptoverif implementation/ssh/ssh.ocv > implementation/ssh/ssh.out
egrep '(RESULT|All)' implementation/ssh/ssh.out | grep -v "RESULT time"
echo "Second, proving secrecy of the exchanged keys: IVs, encryption keys, MAC keys"
./cryptoverif implementation/ssh/ssh-secrecy-key-IVCC.ocv > implementation/ssh/ssh-secrecy-key-IVCC.out
egrep '(RESULT|All)' implementation/ssh/ssh-secrecy-key-IVCC.out | grep -v "RESULT time"
./cryptoverif implementation/ssh/ssh-secrecy-key-IVSC.ocv > implementation/ssh/ssh-secrecy-key-IVSC.out
egrep '(RESULT|All)' implementation/ssh/ssh-secrecy-key-IVSC.out | grep -v "RESULT time"
./cryptoverif implementation/ssh/ssh-secrecy-key-EKCC.ocv > implementation/ssh/ssh-secrecy-key-EKCC.out
egrep '(RESULT|All)' implementation/ssh/ssh-secrecy-key-EKCC.out | grep -v "RESULT time"
./cryptoverif implementation/ssh/ssh-secrecy-key-EKSC.ocv > implementation/ssh/ssh-secrecy-key-EKSC.out
egrep '(RESULT|All)' implementation/ssh/ssh-secrecy-key-EKSC.out | grep -v "RESULT time"
./cryptoverif implementation/ssh/ssh-secrecy-key-MKCC.ocv > implementation/ssh/ssh-secrecy-key-MKCC.out
egrep '(RESULT|All)' implementation/ssh/ssh-secrecy-key-MKCC.out | grep -v "RESULT time"
./cryptoverif implementation/ssh/ssh-secrecy-key-MKSC.ocv > implementation/ssh/ssh-secrecy-key-MKSC.out
egrep '(RESULT|All)' implementation/ssh/ssh-secrecy-key-MKSC.out | grep -v "RESULT time"

echo Generating implementation...
./cryptoverif -impl -o implementation/ssh implementation/ssh/ssh.ocv
cd implementation/ssh

# rm hk pkS skS trusted_hosts

ocamlopt $CRYPTOKIT -I .. -o server str.cmxa unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml SSH_S.mli SSH_S.ml ssh_server.ml
ocamlopt $CRYPTOKIT -I .. -o client str.cmxa unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml SSH_C.mli SSH_C.ml ssh_client.ml
ocamlopt $CRYPTOKIT -I .. -o keygen str.cmxa unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml SSH_Keygen.mli SSH_Keygen.ml ssh_kgen.ml
ocamlopt $CRYPTOKIT -I .. -o add_key str.cmxa unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml add_key.ml

