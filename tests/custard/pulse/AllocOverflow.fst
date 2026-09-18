module AllocOverflow
#lang-pulse
open Pulse
module V  = Pulse.Lib.Vec
module SZ = FStar.SizeT

(* Section 116.  [V.alloc] bounds no length, so [n * sizeof(elt)] is a product
   a verified program can make wrap: [malloc] then succeeds with a small block
   and the fill loop writes [n] elements into it.  karamel emits
   KRML_CHECK_SIZE here; the guard below is Custard's. *)

fn run (n:SZ.t)
  returns r:SZ.t
{
  let v = V.alloc 7ul n;
  V.free v;
  n
}

fn main () returns r:SZ.t
{
  let k = run 4sz;
  if (k = 4sz) { 0sz } else { 1sz }
}
