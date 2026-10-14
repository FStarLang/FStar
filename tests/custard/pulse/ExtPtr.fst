module ExtPtr
#lang-pulse
open Pulse
open FStar.Attributes
module U8 = FStar.UInt8
module I32 = FStar.Int32
module R = Pulse.Lib.Reference

(* Section 57.1: an extern returning a pointer.  A C macro over untyped
   memory hands back [void *], which C converts silently and C++ rejects,
   so the call site has to carry the cast.  The pointer is a Pulse
   reference: an ML [ref] is garbage-collected, and C has no collector. *)

[@@custard_extern "extptr_base"; custard_c_header "ExtPtr_stubs.h"]
assume val base (off : FStar.SizeT.t)
  : stt (R.ref U8.t) emp (fun p -> R.pts_to p 7uy)

fn main ()
  returns r : I32.t
{
  let p = base 0sz;
  let v = !p;
  drop_ (R.pts_to p 7uy);
  if (U8.eq v 7uy) { 0l } else { 1l }
}
