module Ex06e
//insertion-sort

(* Check that a list is sorted *)
val sorted: list int -> Tot bool
let rec sorted l = match l with
    | [] -> true
    | [x] -> true
    | x::y::xs -> (x <= y) && (sorted (y::xs))

(* Definition of the [mem] function *)
val mem: int -> list int -> Tot bool
let rec mem a l = match l with
  | [] -> false
  | hd::tl -> hd=a || mem a tl

(* Exercise: implement insertion sort and prove its partial correctness *)
val sort : l:list int -> Tot (m:list int{sorted m /\ (forall x. mem x l == mem x m)})
