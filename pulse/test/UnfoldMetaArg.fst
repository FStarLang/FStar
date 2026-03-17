module UnfoldMetaArg

#lang-pulse
open Pulse
open FStar.Tactics.V2

let my_pts_to (r : ref int) (#[exact (`1.0R)] f:perm) (v:int) : slprop =
  Pulse.Lib.Reference.pts_to r #f v

fn add1 (r : ref int)
  preserves my_pts_to r 1
{
  unfold my_pts_to;
  (* ^ Used to fail with
  * Error 228:
  - 'norm_term' failed
  - Cannot type Pulse.Lib.Reference.pts_to ?r ?p ?n in context [x; x; x; x; x]
  - Expected a function.
  - Got an expression of type: Pulse.Lib.Core.slprop
  - See also Pulse.Checker.AssertWithBinders.fst:152.15-152.73
  *)
  fold   my_pts_to;
  ();
}
