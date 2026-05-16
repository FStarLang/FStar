module IllTypedInvariant
#lang-pulse
open Pulse.Lib.Pervasives

// While loop with invariant that can't be established initially
[@@expect_failure [19]]
fn bad_invariant ()
  requires emp
  ensures emp
{
  let mut i = 0;
  while (!i < 10)
  invariant pure (!i >= 0 /\ !i <= 10 /\ 1 = 2)
  {
    i := !i + 1;
  }
}
