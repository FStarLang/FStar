#light "off"
module FStar.Hash
open FStar.All
type hash_code
val of_int : int -> hash_code
val of_string : string -> hash_code
val mix : hash_code -> hash_code -> hash_code

type hashtable<'a>
type cmp<'a> = 'a -> 'a -> bool

val create : cmp<'a> -> hashtable<'a>
val insert : hash_code -> 'a -> hashtable<'a> -> unit
val lookup : hash_code -> hashtable<'a> -> option<'a>
