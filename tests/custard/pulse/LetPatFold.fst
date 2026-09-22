module LetPatFold
#lang-pulse
open Pulse
module U32 = FStar.UInt32
module SZ = FStar.SizeT

(* Section 129.  [let (a, (b, _)) = p] binds the scrutinee to [_letpattern]
   and matches it, so a caller that builds the tuple for an
   [inline_for_extraction] callee that immediately takes it apart used to
   build it, name it and read it back out.  The tuple here is the shape a
   type-level fold over a list produces: a [unit] tail, and one pair per
   element. *)

inline_for_extraction
fn body (p : U32.t & (U32.t & unit))
  requires emp
  returns  _:U32.t
  ensures  emp
{
  let (a, (b, _)) = p;
  U32.add_mod a b
}

fn entry (x:U32.t)
  requires emp
  returns  _:U32.t
  ensures  emp
{
  body (x, (U32.add_mod x 1ul, ()))
}

fn main () returns r:SZ.t
{
  let k = entry 3ul;
  if (k = 7ul) { 0sz } else { 1sz }
}
