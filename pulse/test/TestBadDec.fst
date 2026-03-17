module TestBadDec
open Pulse
#lang-pulse

(* This should FAIL: the measure !i increases, so it doesn't decrease *)
[@@expect_failure]
fn test_bad_decreases () {
  let mut i = 0;
  while (!i < 10)
    invariant live i
    invariant pure (!i <= 10)
    decreases !i
  {
    i := !i + 1;
  }
}
