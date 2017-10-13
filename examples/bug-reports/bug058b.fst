module Bug058b

(* Write the fibonacci function and several types for it. *)

val sub_fibo : x:nat -> n:int{n >0 /\ n <= x}  -> int -> int -> Tot int (decreases (x-n))
let rec sub_fibo x n acc1 acc2 =
  if n = x
  then (acc1 + acc2)
  else sub_fibo x (n+1) acc2 (acc1 + acc2)

val fibonacci: (x:int{x>=0}) -> Tot int
let fibonacci x =
  if x <= 1
  then 1
  else sub_fibo x 2 1 1
