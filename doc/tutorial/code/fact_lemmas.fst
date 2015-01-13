module FactLemmas

val factorial : nat -> Tot (x:int{x>0})
let rec factorial n = if n = 0 then 1 else n * factorial (n - 1)


val factorial_is_positive: x:nat -> Tot (u:unit{factorial x > 0})
let rec factorial_is_positive x =
  match x with
  | 0 -> ()
  | _ -> factorial_is_positive (x - 1)


//val factorial_is_monotone: x:nat{x > 2} -> Tot (u:unit{factorial x > x})
//val factorial_is_monotone: x:nat -> Lemma (requires (x > 2))
//                                          (ensures (factorial x > x))
let rec factorial_is_monotone x =
  match x with
  | 3 -> ()
  | _ -> factorial_is_monotone (x - 1)
