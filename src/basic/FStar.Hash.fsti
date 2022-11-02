module FStar.Hash
open FStar.Compiler.Effect

type hash_code

val of_int : int -> hash_code
val of_string : string -> hash_code
val mix : hash_code -> hash_code -> hash_code
val string_of_hash_code : hash_code -> string
