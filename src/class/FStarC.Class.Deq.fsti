module FStarC.Class.Deq

open FStarC.Effect

class deq (a:Type) = {
  (=?) : a -> a -> bool;
}

val (<>?) : #a:Type -> {| deq a |} -> a -> a -> bool

instance val deq_int    : deq int
instance val deq_bool   : deq bool
instance val deq_unit   : deq unit
instance val deq_string : deq string

instance val deq_option
   (_ : deq 'a)
: Tot (deq (option 'a))

instance val deq_list
   (_ : deq 'a)
: Tot (deq (list 'a))

instance val deq_either
   (_ : deq 'a)
   (_ : deq 'b)
: Tot (deq (either 'a 'b))

instance val deq_tuple2
   (_ : deq 'a)
   (_ : deq 'b)
: Tot (deq ('a & 'b))

instance val deq_tuple3
   (_ : deq 'a)
   (_ : deq 'b)
   (_ : deq 'c)
: Tot (deq ('a & 'b & 'c))

instance val deq_tuple4
   (_ : deq 'a)
   (_ : deq 'b)
   (_ : deq 'c)
   (_ : deq 'd)
: Tot (deq ('a & 'b & 'c & 'd))

instance val deq_tuple5
   (_ : deq 'a)
   (_ : deq 'b)
   (_ : deq 'c)
   (_ : deq 'd)
   (_ : deq 'e)
: Tot (deq ('a & 'b & 'c & 'd & 'e))

instance val deq_tuple6
   (_ : deq 'a)
   (_ : deq 'b)
   (_ : deq 'c)
   (_ : deq 'd)
   (_ : deq 'e)
   (_ : deq 'f)
: Tot (deq ('a & 'b & 'c & 'd & 'e & 'f))

