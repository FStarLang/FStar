(*
   Copyright 2023 Microsoft Research

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

module Pulse.Lib.Primitives
#lang-pulse

open PulseCore.Observability
open Pulse.Lib.Core
open PulseCore.FractionalPermission
open Pulse.Lib.Reference
open FStar.Ghost
open Pulse.Class.PtsTo

module U32 = FStar.UInt32
module B = Pulse.Lib.Box

/// This module provides primitive atomic operations.  They have no
/// extractable implementation: Pulse.Lib.Primitives-model.fst is only a
/// sequential model, and must never be compiled.  Extracted code calls
/// [read_atomic], [write_atomic] and [cas] as externals, which are
/// implemented by handwritten code: for C, as static inline functions in
/// share/pulse/runtime/Pulse_Lib_Primitives_runtime.h, which must be
/// included before the extracted code (with Karamel, use the options
/// `-library Pulse.Lib.Primitives -add-include
/// '"Pulse_Lib_Primitives_runtime.h"'`; with Custard's C backend, compile
/// with `-include Pulse_Lib_Primitives_runtime.h`).  There is no OCaml
/// implementation.

val read_atomic (r:ref U32.t) (#n:erased U32.t) (#p:perm)
  : stt_atomic U32.t #Observable emp_inames
    (pts_to r #p n)
    (fun x -> pts_to r #p n ** pure (x == reveal n))

val write_atomic (r:ref U32.t) (x:U32.t)
  : stt_atomic unit #Observable emp_inames
        (pts_to_uninit r) 
        (fun _ -> pts_to r (hide x))

let cond b (p q:slprop) = if b then p else q

val cas (r:ref U32.t) (u v:U32.t) (#i:erased U32.t)
  : stt_atomic bool #Observable emp_inames 
    (pts_to r i)
    (fun b ->
      cond b (pts_to r v ** pure (reveal i == u)) 
             (pts_to r i))

inline_for_extraction
atomic fn read_atomic_box (r:B.box U32.t) (#n:erased U32.t) (#p:perm)
  preserves r |-> Frac p n
  returns x:U32.t
  ensures pure (reveal n == x)
{
  B.to_ref_pts_to r;
  let x = read_atomic (B.box_to_ref r);
  B.to_box_pts_to r;
  x
}

inline_for_extraction
atomic fn write_atomic_box (r:B.box U32.t) (x:U32.t) (#n:erased U32.t)
  requires r |-> n
  ensures r |-> x
{
  B.to_ref_pts_to r;
  write_atomic (B.box_to_ref r) x;
  B.to_box_pts_to r;
}

inline_for_extraction
atomic fn cas_box (r:B.box U32.t) (u v:U32.t) (#i:erased U32.t)
  requires r |-> i
  returns b: bool
  ensures cond b ((r |-> v) ** pure (reveal i == u)) (r |-> i)
{
  B.to_ref_pts_to r;
  let b = cas (B.box_to_ref r) u v;
  if (b) {
    unfold cond;
    B.to_box_pts_to r;
    fold cond true ((r |-> v) ** pure (reveal i == u)) (r |-> i);
    b
  } else {
    unfold cond;
    B.to_box_pts_to r;
    fold cond false ((r |-> v) ** pure (reveal i == u)) (r |-> i);
    b
  }
}
