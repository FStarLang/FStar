module Ex03b
//fibonacci


(* val fibonacci : int -> int *)
(* val fibonacci : int -> ML int (same as above) *)
(* val fibonacci : int -> Tot nat *)
(* val fibonacci : int -> Tot (y:int{y>=1}) *)
(* val fibonacci : x:int -> Tot (y:int{y>=1 /\ y >= x}) *)
(* val fibonacci : x:int -> Tot *)
(*   (y:int{y >= 1 /\ y >= x /\ (x>=3 ==> y>=2)}) *)
val fibonacci : int -> Tot (x:nat{x>0})
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)
