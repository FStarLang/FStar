module Test.CanonCommMonoidSimple.Equiv

open FStar.Algebra.CommMonoid.Equiv
open FStar.Tactics.V2
open FStar.Tactics.CanonCommMonoidSimple.Equiv
open FStar.Mul

(***** Example *)

let test1 (a b c d : int) =
  assert (0 + 1 + a + b + c + d + 2 == (b + 0) + 2 + d + (c + a + 0) + 1) by (
    canon_monoid (quote equality_equiv int) (`int_plus_cm)
  )

// GM 23/Aug/2024: Tried to restore this but it's failing even before the
// changes I was testing, leaving out.
// let test2 =
//   assert (forall (a b c d : int). ((b + 1) * 1) * 2 * a * (c * a) * 1 == a * (b + 1) * c * a * 2) by (
//     ignore (forall_intros());
//     canon_monoid (quote equality_equiv int) (`int_multiply_cm)
//   )
