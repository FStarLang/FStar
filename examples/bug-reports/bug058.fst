module Bug058

(* Write the fibonacci function and several types for it. *)
val fibonacci: (x:int{x>=0}) -> Tot (y:int{y>=0})

let fibonacci x =
   let rec sub_fibo : n:nat{n <= x}  -> nat -> nat -> Tot nat (decreases (x-n)) =
     fun n -> fun acc1 -> fun acc2 ->
         if n = x
         then (acc1 + acc2)
         else sub_fibo (n+1) acc2 (acc1 + acc2)
   in

  if x <= 1
  then 1
  else sub_fibo 2 1 1
