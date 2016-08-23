module Ex04a
//append-intrinsic-type

val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl


(* Give append a type that proves it always returns a list whose
   length is the sum of the lengths of its arguments. *)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2
