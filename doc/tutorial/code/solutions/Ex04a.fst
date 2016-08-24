module Ex04a
//append-intrinsic-type

val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl

val append : l1:list 'a -> l2:list 'a -> Tot (l:list 'a{length l = length l1 + length l2})
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2
