module Test.CanonCommSemiring

open FStar.Mul
open FStar.Tactics.V2
open FStar.Tactics.CanonCommSemiring

#set-options "--tactic_trace_d 0 --no_smt"

let test (a:int) =
  assert (a + - a + 2 * a + - a == -a + 2 * a) by (int_semiring ())
