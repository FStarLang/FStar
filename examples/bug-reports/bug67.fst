module AppendSumLengths

val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl

(* Give append a type that proves it always returns a list whose
   length is the sum of the lengths of its arguments. *)

(* val append : l1:(list 'a) -> l2:(list 'a) -> l3:(list 'a){(length l1) + (length l2) = length l3} *)


val append : l1:(list 'a) -> Tot (l2:(list 'a) -> Tot (l3:(list 'a){(length l1) + (length l2) = (length l3)}))
let rec append l1 l2 = (match l1 with
  | [] -> l2
  | hd :: tl -> (hd :: append tl l2))

val mem : 'a -> list 'a -> Tot bool
let rec mem x l = (match l with
  | [] -> false
  | y::tl -> (if x = y
	     then true
	     else mem x tl))
