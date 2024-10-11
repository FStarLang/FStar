module FStarC.Class.Hashable

open FStarC.Hash
include FStarC.Hash
open FStarC.Class.Show
open FStarC.Class.Deq
open FStarC.Class.Ord

class hashable (a:Type) = {
  hash : a -> hash_code;
}

(* Properties about hash_code, better moved elsewhere. *)
instance val showable_hash_code : showable hash_code
instance val eq_hash_code  : deq hash_code
instance val ord_hash_code : ord hash_code

instance val hashable_int    : hashable int
instance val hashable_string : hashable string
instance val hashable_bool   : hashable bool

instance val hashable_list
  (_ : hashable 'a)
: Tot (hashable (list 'a))

instance val hashable_option
  (_ : hashable 'a)
: Tot (hashable (option 'a))

instance val hashable_either
  (_ : hashable 'a)
  (_ : hashable 'b)
: Tot (hashable (either 'a 'b))

instance val hashable_tuple2
  (_ : hashable 'a)
  (_ : hashable 'b)
: Tot (hashable ('a & 'b))

instance val hashable_tuple3
  (_ : hashable 'a)
  (_ : hashable 'b)
  (_ : hashable 'c)
: Tot (hashable ('a & 'b & 'c))

instance val hashable_tuple4
  (_ : hashable 'a)
  (_ : hashable 'b)
  (_ : hashable 'c)
  (_ : hashable 'd)
: Tot (hashable ('a & 'b & 'c & 'd))

instance val hashable_tuple5
  (_ : hashable 'a)
  (_ : hashable 'b)
  (_ : hashable 'c)
  (_ : hashable 'd)
  (_ : hashable 'e)
: Tot (hashable ('a & 'b & 'c & 'd & 'e))

instance val hashable_tuple6
  (_ : hashable 'a)
  (_ : hashable 'b)
  (_ : hashable 'c)
  (_ : hashable 'd)
  (_ : hashable 'e)
  (_ : hashable 'f)
: Tot (hashable ('a & 'b & 'c & 'd & 'e & 'f))
