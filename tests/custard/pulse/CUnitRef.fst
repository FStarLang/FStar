module CUnitRef
#lang-pulse
open Pulse
module R = Pulse.Lib.Reference

(* Section 123.  Nothing here is public and no type mentions it, so the one
   [custard_unit] in the unit is in the source and the header does not carry
   the typedef. *)

fn get (r : R.ref unit) (#v : erased unit)
  preserves R.pts_to r v
{
  let _ = !r;
  ()
}

fn main ()
  returns x : UInt32.t
{
  let mut r = ();
  r := ();
  get r;
  0ul
}
