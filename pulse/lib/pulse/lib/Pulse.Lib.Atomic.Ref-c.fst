(*
   Copyright 2026 Microsoft Research

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

module Pulse.Lib.Atomic.Ref
#lang-pulse

friend Pulse.Lib.Atomic

open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Ghost
open Pulse.Class.PtsTo
open Pulse.Lib.Atomic
module R = Pulse.Lib.Reference

(* [atomic_ref t] is [ref (atomic_t t)] on C (Pulse.Lib.Atomic-c.fst). *)
let of_ref r = r

ghost
fn to_atomic_ref_pts_to (#t: Type0) (r: R.ref (atomic_t t)) (#p: perm) (#v: t)
  requires R.pts_to r #p (to_atomic v)
  ensures  of_ref r |-> Frac p v
{
  fold pts_to (of_ref r) #p v;
}

ghost
fn of_atomic_ref_pts_to (#t: Type0) (r: R.ref (atomic_t t)) (#p: perm) (#v: t)
  requires of_ref r |-> Frac p v
  ensures  R.pts_to r #p (to_atomic v)
{
  unfold pts_to (of_ref r) #p v;
}
