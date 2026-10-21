module CastSubscript
#lang-pulse
open Pulse
open FStar.Attributes
module U32 = FStar.UInt32
module I32 = FStar.Int32
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module Seq = FStar.Seq

(* Pure getters are inlined into the reads and writes, exposing their casts. *)
[@@custard_extern "cast_subscript_ref"; custard_c_header "CastSubscript_stubs.h"]
assume val ref_base (off:FStar.SizeT.t) : R.ref U32.t

[@@custard_extern "cast_subscript_array"; custard_c_header "CastSubscript_stubs.h"]
assume val array_base (off:FStar.SizeT.t) : A.array U32.t

fn main ()
  requires R.pts_to (ref_base 0sz) 7ul **
           A.pts_to (array_base 0sz) (Seq.create 2 19ul)
  returns r:I32.t
  ensures R.pts_to (ref_base 0sz) 11ul **
          A.pts_to (array_base 0sz) (Seq.upd (Seq.create 2 19ul) 1 29ul)
{
  let before = R.read (ref_base 0sz);
  R.write (ref_base 0sz) 11ul;
  let after = R.read (ref_base 0sz);
  A.pts_to_len (array_base 0sz);
  let array_before = A.op_Dot_Lparen_Rparen (array_base 0sz) 1sz;
  A.op_Dot_Lparen_Rparen_Less_Minus (array_base 0sz) 1sz 29ul;
  let array_after = A.op_Dot_Lparen_Rparen (array_base 0sz) 1sz;
  if (U32.eq before 7ul && U32.eq after 11ul &&
      U32.eq array_before 19ul && U32.eq array_after 29ul)
  { 0l } else { 1l }
}
