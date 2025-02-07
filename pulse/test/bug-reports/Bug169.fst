module Bug169

#lang-pulse
open Pulse

// - Failed to desugar pulse extension text
let is_sublist (a b : Seq.seq nat) : prop = true

[@@expect_failure [72]]
fn check_is_sublist (m: SiveT.t)
  requires emp
  ensures emp
{
  ()
}
