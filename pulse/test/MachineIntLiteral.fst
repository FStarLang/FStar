module MachineIntLiteral
#lang-pulse
open Pulse
open Pulse.Lib.Reference

(* When Pulse checks a slprop, a machine-integer literal such as [7l]
   unfolds to [FStar.Int32.int_to_t 7], whose range guard [FStar.Int.size 7 32]
   the simplifier decides without SMT.  The range is still checked: an
   out-of-range argument to [uint_to_t] or [int_to_t] is rejected. *)

#push-options "--no_smt"
fn lit_int32 (r: ref FStar.Int32.t)
  requires exists* v. pts_to r v
  ensures pts_to r (-7l)
{
  r := (-7l);
}

fn lit_uint32 (r: ref FStar.UInt32.t)
  requires pts_to r 'v
  ensures exists* v. pts_to r v
{
  let x = !r;
  if (FStar.UInt32.rem x 4096ul = 0ul) { r := 1ul } else { r := 2ul }
}

fn explicit_in_range (r: ref FStar.UInt8.t)
  requires pts_to r 'v
  ensures pts_to r 255uy
{
  r := FStar.UInt8.uint_to_t 255;
}
#pop-options

[@@expect_failure [19]]
fn explicit_too_large (r: ref FStar.UInt8.t)
  requires pts_to r 'v
  ensures exists* v. pts_to r v
{
  r := FStar.UInt8.uint_to_t 256;
}

[@@expect_failure [19]]
fn explicit_too_small (r: ref FStar.Int8.t)
  requires pts_to r 'v
  ensures exists* v. pts_to r v
{
  r := FStar.Int8.int_to_t (-129);
}
