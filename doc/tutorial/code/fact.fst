module Factorial

type nat = x:int{x >= 0}

// val factorial : int ->  ML int // F* infers this type by default
// val factorial : int ->  ML (x:int{x >= 1} // strong result type
// val factorial : int ->  x:int{x >= 1} // same as above
// val factorial : int -> Tot int // bad type, factorial not total by default
// val factorial : nat -> Tot int // need to restrict domain to prove totality
val factorial : nat -> Tot nat // stronger result type
// val factorial : nat -> Tot (x:int{x >= 1}) // even stronger result type
let rec factorial n = if n = 0 then 1 else n * factorial (n - 1)

(* We can also prove factorial_monotone intrinsically *)

(* using refinements; note we needed to change the code, not just the type! *)
val factorial_monotone: n:int{n>2} -> Tot (m:nat{m > n})
let rec factorial_monotone n =
  if n = 3 then 6 else n * factorial_monotone (n - 1)

(* can't use assert because we don't expose inductive hypothesis; ill typed
val factorial_monotone_assert: n:int{n>2} -> Tot nat
let rec factorial_monotone_assert n =
  let m = if n = 3 then 6 else n * factorial_monotone_assert (n - 1) in
  assert (m>n); m
*)


