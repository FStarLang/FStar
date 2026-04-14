module LoopDecreases
open Pulse
#lang-pulse

(* Basic while loop with a decreases clause *)
fn test_basic_decreases () {
  let mut i = 0;
  while (!i < 10)
    invariant live i
    invariant pure (!i <= 10)
    decreases (10 - !i)
  {
    i := !i + 1;
  }
}

(* Decreases with loop_requires *)
fn test_decreases_with_requires () {
  let mut i = 0;
  while (!i < 10)
    invariant live i
    invariant pure (!i <= 10)
    requires (!i >= 0)
    decreases (10 - !i)
  {
    i := !i + 1;
  }
}

(* Decreases with no other invariants *)
fn test_decreases_only () {
  let mut i = 10;
  while (!i > 0)
    invariant live i
    decreases !i
  {
    i := !i - 1;
  }
}
