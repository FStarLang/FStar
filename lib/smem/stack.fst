(*--build-config
  variables:LIB=..;
  other-files: $LIB/list.fst
 --*)

module Stack
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

open List

type Stack (a:Type) = list a

val push : #a:Type -> Stack a -> a -> Tot (Stack a)
let push st e = e :: st

(*
val pop : #a:Type -> l:(Stack a){ 0 < (length l)} -> Tot (a * (Stack a))
let pop l = ((hd l), tail l)
*)

val pop : #a:Type -> Stack a -> Tot (option (a * (Stack a)))
let pop st =
match st with
| nil -> None
| h::tl -> Some (h, tl)

val stail : #a:Type -> Stack a -> Tot (Stack a)
let stail st =
match st with
| nil -> []
| h::tl -> tl

val snonempty : #a:Type -> Stack a -> Tot bool
let snonempty st =
match st with
| nil -> false
| h::tl -> true

val top : #a:Type -> l:(Stack a){ (snonempty l) == true} -> Tot a
let top l =
match l with
| nil -> (admit ()) (*HELP!!*)
| h::tl -> h

(*BUG: the following is incorrectly acccepted
val top : #a:Type -> l:(Stack a){ (snonempty l) == true} -> Tot ((a * (Stack a)))
let top l =
match l with
| nil -> (admit ())
| h::tl -> h
 *)


(*
val top : #a:Type -> l:(Stack a){ 0 < (length l)} -> Tot (a * (Stack a))
let top l =
match l with
| nil => ()
| h::tl => h

val top : #a:Type -> l:(Stack a){ (l = nil) -> False } -> Tot (a * (Stack a))
let top l =
match l with
| nil => ()
| h::tl => h
*)

(*unlike OCaml, match ... with.. does not need an end*)

(* not needed for now

assume logic val top : #a:Type -> Stack a -> Tot (option (a * (Stack a)))
type isTop (#a : Type) (t:a) (s : Stack a)  = (top s == (Some t))
*)
