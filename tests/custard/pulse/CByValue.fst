module CByValue
#lang-pulse
open Pulse
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module I32 = FStar.Int32
module B = Pulse.Lib.Box

(* Section 18.4: a field held *by value* needs the definition of its type, not
   just the tag, so the definitions have to be topologically sorted -- and the
   order Custard receives is the SCC pass's, computed over *all* dependencies,
   so a group made cyclic by a *pointer* is one SCC whose internal order is
   arbitrary.

   That is exactly this shape, and it is EverParse's: [raw] reaches [arr] by
   value, [arr] reaches [slice raw] by value, and [slice raw] closes the cycle
   back to [raw] through a pointer.  The by-value edges are necessarily
   acyclic -- that is what [check_finite] establishes -- so a topological
   order of them always exists.

   [slice] is *polymorphic*, and that is what makes the test bite rather than
   pass by luck.  A source bundle of mutually recursive types is already
   ordered by dependency, so no ordering of [type ... and ...] reproduces it;
   [slice raw] is a monomorphized instance, created when the request for [arr]
   reaches it, and so lands after the type that holds it. *)

noeq type slice (a:Type0) = { s_base : B.box a; s_len : U32.t }

noeq type raw =
  | Int  : U8.t -> raw
  | Arr  : arr -> raw
and arr = { a_len : U8.t; a_ptr : slice raw }

let len_of (r : raw) : U32.t =
  match r with
  | Int _ -> 0ul
  | Arr a -> a.a_ptr.s_len

let byte_of (r : raw) : U8.t =
  match r with
  | Int b -> b
  | Arr _ -> 0uy

fn head_of (s : slice raw) (#v : erased raw)
  preserves B.pts_to s.s_base v
  returns b : U8.t
{
  let x = B.op_Bang s.s_base;
  byte_of x
}

fn main ()
  returns r : I32.t
{
  let p = B.alloc (Int 9uy);
  let s = { s_base = p; s_len = 3ul };
  let r = Arr ({ a_len = 1uy; a_ptr = s });
  rewrite each p as s.s_base;
  let h = head_of s;
  rewrite each s.s_base as p;
  B.free p;
  if (U32.eq (len_of r) 3ul && U8.eq h 9uy) { 0l } else { 1l }
}
