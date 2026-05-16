module InvariantPayload
#lang-pulse
open Pulse.Lib.Pervasives

// Fold/unfold invariant with wrong payload
let my_pred (r: ref int) : slprop = exists* v. pts_to r v ** pure (v > 0)

[@@expect_failure [19]]
fn inv_payload_fail (r: ref int)
  requires pts_to r 0
  ensures my_pred r
{
  fold my_pred r;  // ERROR: can't prove v > 0 with v = 0
  ()
}
