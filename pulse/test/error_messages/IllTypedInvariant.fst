module IllTypedInvariant
#lang-pulse
open Pulse.Lib.Pervasives

// While loop with invariant that can't be established initially
// The loop has no [decreases], so the function has to be [divergent]; without
// that this reports the effect mismatch instead of the invariant failure this
// test is about.
[@@expect_failure [19]]
divergent fn bad_invariant ()
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
