open Base
open Crypto

type type_oracle_OStart = unit -> (unit * pkey)
val init : unit -> (type_oracle_OStart)
