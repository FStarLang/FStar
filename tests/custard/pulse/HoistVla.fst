module HoistVla
#lang-pulse
open Pulse
module A = Pulse.Lib.Array
module SZ = FStar.SizeT

fn run (n:SZ.t)
  requires pure (SZ.v n > 0)
  returns r:FStar.UInt32.t
{
  let mut result = 0ul;
  let a = A.alloc 7ul n;
  A.pts_to_len a;
  let x = a.(0sz);
  A.free a;
  result := x;
  !result
}

fn main () returns r:FStar.Int32.t
{
  let x = run 3sz;
  if (FStar.UInt32.eq x 7ul) { 0l } else { 1l }
}
