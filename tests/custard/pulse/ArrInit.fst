(* Section 94.  A local array whose length and fill are both constants is
   what C's initializer syntax is for, and Custard wrote a loop for every one
   of them.  The four shapes are here together because what makes this a
   change worth pinning is the *boundary*, not the good case: [zeroes] and
   [sevens] take an initializer, and [varfill] and [varlen] must keep the
   loop, one because C has no way to repeat a runtime value and the other
   because a variable-length array may not be initialized at all. *)
module ArrInit
#lang-pulse
open Pulse
module A  = Pulse.Lib.Array
module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn zeroes ()
  returns r: U8.t
{
  let a = A.alloc 0uy 8sz;
  A.pts_to_len a;
  let v = a.(3sz);
  A.free a;
  v
}

fn sevens ()
  returns r: U8.t
{
  let a = A.alloc 7uy 4sz;
  A.pts_to_len a;
  let v = a.(2sz);
  A.free a;
  v
}

fn varfill (x: U8.t)
  returns r: U8.t
{
  let a = A.alloc x 4sz;
  A.pts_to_len a;
  let v = a.(1sz);
  A.free a;
  v
}

fn varlen (n: SZ.t)
  requires pure (SZ.v n > 3)
  returns r: U8.t
{
  let a = A.alloc 0uy n;
  A.pts_to_len a;
  let v = a.(3sz);
  A.free a;
  v
}

fn main ()
  returns x: FStar.Int32.t
{
  let a = zeroes ();
  let b = sevens ();
  let c = varfill 5uy;
  let d = varlen 9sz;
  if (U8.eq a 0uy && U8.eq b 7uy && U8.eq c 5uy && U8.eq d 0uy) { 0l } else { 1l }
}
