module EarlyReturnVla
#lang-pulse
open Pulse
module A = Pulse.Lib.Array
module SZ = FStar.SizeT

(* A variable-length array declared after an early return: goto mode would
   jump into its scope. *)
fn run (n:SZ.t)
  returns r:FStar.UInt32.t
{
  if (SZ.eq n 0sz) {
    0ul
  } else {
    let a = A.alloc 7ul n;
    A.pts_to_len a;
    let x = a.(0sz);
    A.free a;
    x
  }
}

fn main () returns r:FStar.Int32.t
{
  let x = run 3sz;
  let y = run 0sz;
  if (FStar.UInt32.eq x 7ul && FStar.UInt32.eq y 0ul) { 0l } else { 1l }
}
