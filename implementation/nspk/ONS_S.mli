open Base
open Crypto

type type_oracle_OS13 = (string * string) -> (unit * pkey * string * string)
val init : unit -> (type_oracle_OS13)
