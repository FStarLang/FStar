(*
   Copyright 2008-2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

(* Section 20.  A slice, split in two, written through and copied across.

   The body is [pulse/test/Example.Slice.fst], which is the program the bug
   was reported against (section 19.15), with a [main] that checks the bytes
   rather than returning them.  That is what distinguishes the fix from the
   bug: before it the Rust output either failed to borrow-check or -- with the
   borrows silenced the way rustc suggests -- wrote through a deep copy that
   was then dropped, so every byte read back as zero while the C output gave
   the right answer.

   The same source has to compile two ways.  Under [--custard_backend KrmlC]
   the F* definition of [Pulse.Lib.Slice] is the implementation and the result
   is a struct of a pointer and a length.  Under [KrmlRust] karamel supplies
   the type itself, as Rust's own borrowed slice, and Custard's job is to
   leave it alone for karamel to recognize. *)
module PulseSlice
#lang-pulse
open Pulse
open Pulse.Lib.Trade
open Pulse.Lib.Slice.Util
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
open Pulse { pts_to } (* restore pts_to, shadowed by Pulse.Lib.Slice.Util *)

(* [s0] is taken up to [Seq.equal] rather than syntactically so that the
   caller can arrive with whatever chain of updates it built the array from;
   the body is [Example.Slice.test] unchanged. *)
fn test (arr: A.array U8.t) (#s0: erased (Seq.seq U8.t))
    requires pts_to arr s0 ** pure (Seq.equal s0 seq![0uy; 1uy; 2uy; 3uy; 4uy; 5uy])
    ensures exists* s. pts_to arr s ** pure (s `Seq.equal` seq![0uy; 5uy; 4uy; 5uy; 4uy; 5uy])
{
  A.pts_to_len arr;
  let slice = from_array arr 6sz;
  let s' = split slice 2sz;
  match s' {
    s1, s2 -> {
      pts_to_len s1;
      share s2;
      let s2' = subslice_trade s2 1sz 4sz;
      let x = s2'.(len s1);
      s1.(1sz) <- x;
      elim_trade _ _;
      gather s2;
      let s' = split s2 2sz;
      match s' {
        s3, s4 -> {
          pts_to_len s3;
          pts_to_len s4;
          copy s3 s4;
          join s3 s4 s2;
          join s1 s2 slice;
          to_array slice;
        }
      }
    }
  }
}

(* Reads back through the *array*, so a slice operation that wrote into a copy
   rather than into the caller's memory is a nonzero exit status. *)
fn main ()
  returns r:US.t
{
  let arr = A.alloc 0uy 6sz;
  A.pts_to_len arr;
  A.op_Array_Assignment arr 1sz 1uy;
  A.op_Array_Assignment arr 2sz 2uy;
  A.op_Array_Assignment arr 3sz 3uy;
  A.op_Array_Assignment arr 4sz 4uy;
  A.op_Array_Assignment arr 5sz 5uy;
  test arr;
  A.pts_to_len arr;
  let a = A.op_Array_Access arr 1sz;
  let b = A.op_Array_Access arr 2sz;
  let c = A.op_Array_Access arr 4sz;
  A.free arr;
  if (U8.(a =^ 5uy) && U8.(b =^ 4uy) && U8.(c =^ 4uy)) { 0sz } else { 1sz }
}
