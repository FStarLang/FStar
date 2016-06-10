module FirstProofs

val factorial: nat -> Tot nat
let rec factorial n = if n = 0 then 1 else op_Multiply n (factorial (n - 1))

val factorial_is_positive: x:nat -> Tot (u:unit{factorial x > 0})
let rec factorial_is_positive = function
  | 0 -> ()
  | x -> factorial_is_positive (x - 1)

val factorial_is_increasing: x:nat{x >= 2} -> Tot (u:unit{factorial x >= x})
let rec factorial_is_increasing = function
  | 2 -> ()
  | x -> factorial_is_increasing (x - 1)

val factorial_is_doubling: x:nat{x >= 3} -> Tot (u:unit{factorial x >= op_Multiply 2 x})
let rec factorial_is_doubling = function
  | 3 -> ()
  | x -> factorial_is_doubling (x - 1)

// This fails on strider
// val factorial_is_squaring: x:nat{x >= 4} -> Tot (u:unit{factorial x > x * x})
// let rec factorial_is_squaring = function
//   | 4 -> ()
//   | x -> factorial_is_squaring (x - 1)

(* (\* This is getting to be a bit much for Z3 *\) *)
(* val factorial_is_cubing: x:nat{x > 5} -> Tot (u:unit{factorial x >= x * x * x}) *)
(* let rec factorial_is_cubing = function *)
(*   | 6 -> () *)
(*   | x -> factorial_is_cubing (x - 1) *)

val fibonacci: nat -> Tot nat
let rec fibonacci = function
  | 0
  | 1 -> 1
  | n -> fibonacci (n - 1) + fibonacci (n - 2)

val fibonacci_is_increasing: n:nat -> Lemma (requires True)
                                          (ensures (fibonacci n >= n))
                                          []
let rec fibonacci_is_increasing n = if n > 1 then fibonacci_is_increasing (n - 1) else ()
