open Base
open Crypto

type type_oracle_OB9 = (pkey * string * string) -> ((type_oracle_OB11) * string)
 and type_oracle_OB7 = (string) -> ((type_oracle_OB9) * string * string)
 and type_oracle_OB11 = (string) -> unit
val init : unit -> (type_oracle_OB7)
