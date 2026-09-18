(* Section 118.  An array filled with [FStar.Float32.zero].  ulib derives
   [zero] as an [inline_for_extraction let] over [of_int], so what reaches
   the backend is a *cast* of an integer literal, and a cast is not a
   constant: the array lost its brace initializer to a fill loop, and every
   float constant was spelled [(float)0] rather than [0.0f]. *)
module ArrFloat
#lang-pulse
open Pulse
module A = Pulse.Lib.Array
module F = FStar.Float32

fn sum ()
  returns r: F.t
{
  let a = A.alloc F.zero 4sz;
  A.pts_to_len a;
  a.(1sz) <- F.one;
  let v = a.(1sz);
  A.free a;
  F.add v F.zero
}

fn main ()
  returns x: FStar.Int32.t
{
  let v = sum ();
  if (F.lt v (F.of_int 2L)) { 0l } else { 1l }
}
