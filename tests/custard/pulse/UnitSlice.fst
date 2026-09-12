module UnitSlice
#lang-pulse

(* EverParse's shape, reduced.  [nil] has one nullary constructor, so Custard
   erases it to [unit] (section 5.5).  A parser for it still has to *return*
   something, and its caller pairs that something with the rest of the input:

     let x = parse_nil s;
     Some (x, 1sz)

   which is a unit-typed variable in value position -- a tuple component, not
   a call argument.  Section 82's rewrite is scoped to call arguments, so it
   does not reach here, and karamel's Rust printer deletes a unit-typed [let]
   and then cannot print the use of the binder it deleted.

   The read of the slice is what keeps the binding alive: a pure producer is
   inlined and the variable never appears. *)

open Pulse
open Pulse.Lib.Slice

module U8 = FStar.UInt8
module SZ = FStar.SizeT
module S = Pulse.Lib.Slice

type byte = U8.t

type nil = | Mknil0

fn parse_nil (s : S.slice byte) (#p : perm) (#v : erased (Seq.seq byte))
  requires pts_to s #p v
  returns r : nil
  ensures pts_to s #p v
{
  S.pts_to_len s;
  if (SZ.lt 0sz (S.len s)) {
    let b = s.(0sz);
    if (U8.gt b 0uy) { Mknil0 } else { Mknil0 }
  } else { Mknil0 }
}

fn parse_null (s : S.slice byte) (#p : perm) (#v : erased (Seq.seq byte))
  requires pts_to s #p v
  returns r : option (nil & SZ.t)
  ensures pts_to s #p v
{
  let x = parse_nil s;
  Some (x, 1sz)
}

fn main ()
  requires emp
  returns r : FStar.Int32.t
  ensures emp
{
  let mut a = [| 7uy; 4sz |];
  let s = S.from_array a 4sz;
  let o = parse_null s;
  S.to_array s;
  match o {
    Some p -> { if (SZ.gt (snd p) 0sz) { 0l } else { 1l } }
    None -> { 1l }
  }
}
