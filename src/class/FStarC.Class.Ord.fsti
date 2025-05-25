module FStarC.Class.Ord

open FStarC.Effect
open FStarC.Order
include FStarC.Class.Deq
open FStarC.Class.Deq

class ord (a:Type) = {
  super : deq a;
  cmp : a -> a -> order;
}

val sort
  (#a:Type) {| ord a |}
  (xs : list a)
  : list a

val sort_by
  (#a:Type) (f : a -> a -> order)
  (xs : list a)
  : list a

(* Deduplicate elements, preserving order as determined by the leftmost
occurrence. So dedup [a,b,c,a,f,e,c] = [a,b,c,f,e] *)
val dedup
  (#a:Type) {| ord a |}
  (xs : list a)
  : list a

(* Sort and deduplicate at once *)
val sort_dedup
  (#a:Type) {| ord a |}
  (xs : list a)
  : list a

(* Returns the difference of two lists, modulo order and duplication.
The first component is the elements only present in xs, and the second
is the elements only present in ys. *)
val ord_list_diff (#a:Type0) {| ord a |} (xs ys : list a) : list a & list a

instance val ord_eq (a:Type) (d : ord a) : Tot (deq a)

val (<?)  : #a:Type -> {| ord a |} -> a -> a -> bool
val (<=?) : #a:Type -> {| ord a |} -> a -> a -> bool
val (>?)  : #a:Type -> {| ord a |} -> a -> a -> bool
val (>=?) : #a:Type -> {| ord a |} -> a -> a -> bool

val min : #a:Type -> {| ord a |} -> a -> a -> a
val max : #a:Type -> {| ord a |} -> a -> a -> a

instance val ord_int    : ord int
instance val ord_bool   : ord bool
instance val ord_unit   : ord unit
instance val ord_string : ord string

instance val ord_option
   (_ : ord 'a)
: Tot (ord (option 'a))

instance val ord_list
   (_ : ord 'a)
: Tot (ord (list 'a))

instance val ord_either
   (_ : ord 'a)
   (_ : ord 'b)
: Tot (ord (either 'a 'b))

instance val ord_tuple2
   (_ : ord 'a)
   (_ : ord 'b)
: Tot (ord ('a & 'b))

instance val ord_tuple3
   (_ : ord 'a)
   (_ : ord 'b)
   (_ : ord 'c)
: Tot (ord ('a & 'b & 'c))

instance val ord_tuple4
   (_ : ord 'a)
   (_ : ord 'b)
   (_ : ord 'c)
   (_ : ord 'd)
: Tot (ord ('a & 'b & 'c & 'd))

instance val ord_tuple5
   (_ : ord 'a)
   (_ : ord 'b)
   (_ : ord 'c)
   (_ : ord 'd)
   (_ : ord 'e)
: Tot (ord ('a & 'b & 'c & 'd & 'e))

instance val ord_tuple6
   (_ : ord 'a)
   (_ : ord 'b)
   (_ : ord 'c)
   (_ : ord 'd)
   (_ : ord 'e)
   (_ : ord 'f)
: Tot (ord ('a & 'b & 'c & 'd & 'e & 'f))
