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

(* Section 94.4.  A zero-length array: [{ }] is not an initializer C99 accepts
   and [uint8_t a[0]] is not a declaration it accepts either, so this one is
   the reason both guards are written the way they are. *)
fn empty ()
  returns r: U8.t
{
  let a = A.alloc 0uy 0sz;
  A.pts_to_len a;
  A.free a;
  3uy
}

(* Section 101.  The same zero length at an element type that has no
   initializer list: [emptyr] took the loop path, and wrote
   [for (size_t _ci1 = 0; _ci1 < 0; _ci1++)] over the one cell section 94.4
   had to round the declaration up to.  A condition that is false on entry,
   filling a cell no index reaches. *)
noeq type cell = { c_a : U8.t; c_b : U8.t }

fn emptyr ()
  returns r: U8.t
{
  let a = A.alloc ({ c_a = 1uy; c_b = 2uy }) 0sz;
  A.pts_to_len a;
  A.free a;
  4uy
}

fn main ()
  returns x: FStar.Int32.t
{
  let a = zeroes ();
  let b = sevens ();
  let c = varfill 5uy;
  let d = varlen 9sz;
  let e = empty ();
  let f = emptyr ();
  if (U8.eq a 0uy && U8.eq b 7uy && U8.eq c 5uy && U8.eq d 0uy && U8.eq e 3uy
      && U8.eq f 4uy) {
    0l
  } else {
    1l
  }
}
