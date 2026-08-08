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

(* The smallest interesting Pulse program: a stack-allocated reference, a
   while loop, and a heap-allocated vector.  Every one of these goes through
   the Pulse rules of FStarC.Custard.Builtins. *)
module PulseBasic
#lang-pulse
open Pulse
module US = FStar.SizeT
module U32 = FStar.UInt32
module V = Pulse.Lib.Vec

(* A stack-allocated reference plus a while loop. *)
fn count_up (n:US.t)
  returns r:US.t
{
  let mut i = 0sz;
  while (let vi = !i; US.(vi <^ n))
  invariant exists* (vi:US.t). (
    i |-> vi ** pure (US.v vi <= US.v n)
  )
  decreases (US.v n - US.v (!i))
  {
    let vi = !i;
    i := US.(vi +^ 1sz);
  };
  !i
}

(* A heap-allocated vector: alloc, write, read, free. *)
fn vec_roundtrip (x:U32.t)
  returns r:U32.t
{
  let v = V.alloc x 4sz;
  V.op_Array_Assignment v 2sz x;
  let y = V.op_Array_Access v 2sz;
  V.free v;
  y
}

fn main ()
  returns r:US.t
{
  let a = count_up 10sz;
  let b = vec_roundtrip 7ul;
  let _ = b;
  a
}
