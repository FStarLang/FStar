module FStarC.Hash
open FStarC.Effect

type hash_code

(* Unsure whether to expose this. Try not to use it. It's
useful in hashmap to use zarith imaps. *)
val to_int : hash_code -> int

val cmp_hash (_ _ : hash_code) : int

val of_int : int -> hash_code
val of_string : string -> hash_code
val mix : hash_code -> hash_code -> hash_code
val string_of_hash_code : hash_code -> string
