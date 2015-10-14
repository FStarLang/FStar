(*--build-config
    options:--admit_fsi FStar.List --admit_fsi FStar.Set;
    other-files:set.fsi ext.fst heap.fst st.fst all.fst list.fsi
  --*)

(** An implementation of a stack using the list module. *)

module FStar.Stack
type stack (a:Type) = list a

val push : #a:Type -> stack a -> a -> Tot (stack a)
let push st e = e :: st

val tail : #a:Type -> stack a -> Tot (stack a)
let tail st =
  match st with
  | [] -> []
  | h::tl -> tl

let isNonEmpty = is_Cons

val top : #a:Type -> l:stack a{isNonEmpty l} -> Tot a
let top l =
  match l with
  | h::tl -> h

val pop : #a:Type -> l:stack a{isNonEmpty l} -> Tot (a * stack a)
let pop l =
  match l with
  | h::tl -> h,tl
