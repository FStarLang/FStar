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

(* Section 77.  An abbreviation for a slice, declared and never used.

   [ugly] is dead: Custard unfolds every abbreviation at every occurrence, so
   [first] takes a slice structurally and nothing in the program names [ugly].
   Emitting the declaration anyway used to be enough, on its own, to make
   karamel reject *every* function in the program that takes a slice --- it
   reads an abbreviation of an applied type as the chosen name for that
   instance and then rewrites all occurrences of [Pulse.Lib.Slice.slice u8] to
   it, which its Rust backend's native slice arm does not agree with.

   So the test is that the program still compiles at all, and that the alias
   does not appear in the crate. *)
module UglyAlias
#lang-pulse
open Pulse
module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module US = FStar.SizeT
module U8 = FStar.UInt8

let ugly = S.slice U8.t

fn first (s: S.slice U8.t) (#p: perm) (#v: erased (Seq.seq U8.t) { Seq.length v == 2 })
    requires S.pts_to s #p v
    returns  x:U8.t
    ensures  S.pts_to s #p v ** pure (x == Seq.index v 0)
{
  S.pts_to_len s;
  S.op_Dot_Lparen_Rparen s 0sz
}

fn main ()
  returns r:US.t
{
  let arr = A.alloc 7uy 2sz;
  A.pts_to_len arr;
  let s = S.from_array arr 2sz;
  let x = first s;
  S.to_array s;
  A.free arr;
  if (U8.(x =^ 7uy)) { 0sz } else { 1sz }
}
