open Base
open Crypto

type type_oracle_OA5 = (string) -> (unit * string)
 and type_oracle_OA3 = (pkey * string * string) -> ((type_oracle_OA5) * string)
 and type_oracle_OA1 = (string) -> ((type_oracle_OA3) * string * string)
val init : unit -> (type_oracle_OA1)
