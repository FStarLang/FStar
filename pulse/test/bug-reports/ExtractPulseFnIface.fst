module ExtractPulseFnIface
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
module R = Pulse.Lib.Reference

let pure_add (x y : int) : int = x + y

fn pulse_read_ref
  (r: ref int)
  (#v: Ghost.erased int)
  requires R.pts_to r v
  returns x: int
  ensures R.pts_to r v ** pure (x == Ghost.reveal v)
{
  let x = !r;
  x
}
