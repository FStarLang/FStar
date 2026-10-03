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

(* Section 94.5.  An allocation whose fill is [EAny]: an arbitrary value of
   the element type, which is by definition what the uninitialized storage
   already holds.  [Reference.alloc_uninit] and [Array.Core.mask_alloc] are
   the rules that introduce it, and none of the peepholes above can reach it
   -- [EAny] is not an [EConst], so the initializer list is refused whatever
   the element type is, and at [cell] it would be refused anyway.  So both of
   these declared their storage and then wrote a value chosen for being
   arbitrary into every cell of it.  The deprecation on the two rules is about
   their *model* being unsound, not about what they extract to: they are the
   shape a backend plugin reaches for when it wants a local that its own
   intrinsics are about to fill. *)
module R  = Pulse.Lib.Reference
module AC = Pulse.Lib.Array.Core

fn uninit_ref ()
  returns r: U8.t
{
  let p = R.alloc_uninit U8.t ();
  p := 9uy;
  let v = !p;
  R.free p;
  v
}

fn uninit_arr ()
  returns r: U8.t
{
  let a = AC.mask_alloc cell 4sz;
  AC.mask_write a 1sz ({ c_a = 6uy; c_b = 7uy });
  let v = AC.mask_read a 1sz;
  AC.mask_free a;
  v.c_b
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
  let g = uninit_ref ();
  let h = uninit_arr ();
  if (U8.eq a 0uy && U8.eq b 7uy && U8.eq c 5uy && U8.eq d 0uy && U8.eq e 3uy
      && U8.eq f 4uy && U8.eq g 9uy && U8.eq h 7uy) {
    0l
  } else {
    1l
  }
}
