module CUnitTy
#lang-pulse
open Pulse
module B = Pulse.Lib.Box

(* Section 123.  A [ref unit] is a [custard_unit *], and a type reaches the
   header whether or not any signature is public, so this is the case where
   the typedef has to be in the header. *)

noeq type box = { cell : B.box unit; tag : UInt32.t }

fn mk ()
  returns b : box
  ensures B.pts_to b.cell ()
{
  let c = B.alloc ();
  let b = { cell = c; tag = 0ul };
  rewrite each c as b.cell;
  b
}

fn main ()
  returns r : UInt32.t
{
  let b = mk ();
  B.op_Colon_Equals b.cell ();
  B.free b.cell;
  b.tag
}
