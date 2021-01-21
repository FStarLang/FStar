#light "off"
module FStar.Hash
open FStar.All
type hash_code = H of int
let of_int (_ : int) : hash_code = failwith "TODO"
let of_string (s  : string) : hash_code =  failwith "TODO"
let mix (h0:hash_code) (h1:hash_code) : hash_code = failwith "TODO"
type hashtable<'a> = Dummy
type cmp<'a> = 'a -> 'a -> bool
let create (c:cmp<'a>) : hashtable<'a> = Dummy
let insert (h: hash_code) (x:'a) (ht:hashtable<'a>) = ()
let lookup (h: hash_code) (ht: hashtable<'a>) : option<'a> = None
