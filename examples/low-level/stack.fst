(*--build-config
  variables:LIB=../../lib;
  other-files: $LIB/list.fst
 --*)

module Stack
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

open List

type Stack (a:Type) = list a

val push : #a:Type -> Stack a -> a -> Tot (Stack a)
let push st e = e :: st


val stail : #a:Type -> Stack a -> Tot (Stack a)
let stail st =
match st with
| nil -> []
| h::tl -> tl

let isNonEmpty = is_Cons

val top : #a:Type -> l:(Stack a){ (isNonEmpty l)} -> Tot a
let top l =
match l with
| h::tl -> h

val pop : #a:Type -> l:(Stack a){ (isNonEmpty l)} -> Tot (a * (Stack a))
let pop l =
match l with
| h::tl -> (h,tl)

(*unlike Coq, match ... with.. does have an end*)
