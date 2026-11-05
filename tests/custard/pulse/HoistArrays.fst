module HoistArrays
#lang-pulse
open Pulse
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module V = Pulse.Lib.Vec

noeq type pair = { a: FStar.UInt32.t; b: FStar.UInt32.t }

fn run (n:SZ.t)
  returns r:FStar.UInt32.t
{
  let mut i = 0sz;
  let mut sum = 0ul;
  while (let j = !i; SZ.(j <^ n))
  invariant exists* j s. i |-> j ** sum |-> s ** pure (SZ.v j <= SZ.v n)
  decreases (SZ.v n - SZ.v (!i))
  {
    let j = !i;
    let a = A.alloc 7ul 4sz;
    A.pts_to_len a;
    let x = a.(2sz);
    A.free a;
    let p = A.alloc ({ a = x; b = 3ul }) 2sz;
    A.pts_to_len p;
    let v = p.(1sz);
    A.free p;
    let uninit = R.alloc_uninit FStar.UInt32.t ();
    uninit := v.b;
    let y = !uninit;
    R.free uninit;
    let old = !sum;
    sum := FStar.UInt32.add_mod old (FStar.UInt32.add_mod x y);
    i := SZ.(j +^ 1sz);
  };
  let heap = V.alloc 9ul n;
  V.free heap;
  !sum
}

fn main () returns r:FStar.Int32.t
{
  let x = run 3sz;
  if (FStar.UInt32.eq x 30ul) { 0l } else { 1l }
}
