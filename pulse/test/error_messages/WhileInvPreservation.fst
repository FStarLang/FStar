module WhileInvPreservation
#lang-pulse
open Pulse.Lib.Pervasives

// While loop body fails to preserve invariant
[@@expect_failure [19]]
fn while_inv_fail ()
  requires emp
  ensures emp
{
  let mut i = 0;
  while (let vi = !i; (vi < 10))
  invariant pure (!i >= 0 /\ !i <= 10)
  {
    i := !i + 2  // ERROR: i + 2 might exceed 10, violating invariant
  }
}
