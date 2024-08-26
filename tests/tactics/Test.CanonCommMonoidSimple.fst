module Test.CanonCommMonoidSimple

open FStar.Algebra.CommMonoid
open FStar.Tactics.V2
open FStar.Tactics.CanonCommMonoidSimple
open FStar.Mul

(***** Example *)

let lem0 (a b c d : int) =
  assert (0 + 1 + a + b + c + d + 2 == (b + 0) + 2 + d + (c + a + 0) + 1) by (
    canon_monoid int_plus_cm;
    trefl()
  )

let _ =
  assert (forall (a b c d : int). ((b + 1) * 1) * 2 * a * (c * a) * 1 == a * (b + 1) * c * a * 2) by (
    ignore (forall_intros());
    canon_monoid int_multiply_cm;
    trefl()
  )
