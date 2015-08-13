open Base
open Crypto

type type_oracle_OBGK = unit -> (unit * pkey)
val init : unit -> (type_oracle_OBGK)
