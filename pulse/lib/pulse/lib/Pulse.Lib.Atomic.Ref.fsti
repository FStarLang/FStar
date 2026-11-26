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

(** Atomic cells that live anywhere: a [ref (atomic_t t)] (a pointer to an
    [_Atomic(t)], which may be a local variable, an array element, a struct
    field...) is an [atomic_ref t].

    This module is only implemented on C: on OCaml, [atomic_ref t] is
    [t Atomic.t], and there is no [atomic_t t]. *)

open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Ghost
open Pulse.Class.PtsTo
open Pulse.Lib.Atomic
module R = Pulse.Lib.Reference

val of_ref (#t: Type0) (r: R.ref (atomic_t t)) : atomic_ref t

ghost
fn to_atomic_ref_pts_to (#t: Type0) (r: R.ref (atomic_t t)) (#p: perm) (#v: t)
  requires R.pts_to r #p (to_atomic v)
  ensures  of_ref r |-> Frac p v

ghost
fn of_atomic_ref_pts_to (#t: Type0) (r: R.ref (atomic_t t)) (#p: perm) (#v: t)
  requires of_ref r |-> Frac p v
  ensures  R.pts_to r #p (to_atomic v)
