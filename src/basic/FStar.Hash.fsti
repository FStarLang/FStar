module FStar.Hash
open FStar.Compiler.Effect

type hash_code

val of_int : int -> hash_code
val of_string : string -> hash_code
val mix : hash_code -> hash_code -> hash_code

type hashtable 'a 'b
type cmp 'a = 'a -> 'a -> bool
type hashable 'a = 'a * ('a -> hash_code)
val create : cmp 'a -> hashtable 'a 'b
val insert : hashable 'a -> 'b -> hashtable 'a 'b -> unit
val lookup : hashable 'a -> hashtable 'a 'b -> option 'b
val clear: hashtable 'a 'b -> unit
