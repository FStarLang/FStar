(*
   Copyright 2025 Microsoft Research

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

module Pulse.Lib.CountingSemaphore
#lang-pulse

(**
  A counting semaphore managing indexed resources `on_range p 0 max`.
  
  Design:
  - GhostFractionalTable with bool values tracks per-slot state
  - table[i] = true: semaphore owns p(i), full permission in invariant
  - table[i] = false: client has permit, half permission split
  - Counter tracks number of available resources

  **Current Status:**
  - try_acquire: Working (uses existential for ghost slot index)
  - release: Stub with memory leak
  - share/gather: Working
  - try_free: Stub that always returns false
*)

open Pulse.Lib.Pervasives
open Pulse.Lib.OnRange
open Pulse.Lib.Primitives

module T = FStar.Tactics.V2
module U32 = FStar.UInt32
module CInv = Pulse.Lib.CancellableInvariant
open Pulse.Lib.CancellableInvariant

(** The semaphore capacity must fit in a U32 *)
let sem_max = n:pos{ n <= UInt.max_int 32 }

(** The abstract semaphore type, parameterized by indexed predicate *)
val sem (p: nat -> slprop) : Type0

(** 
  A permit witnessing acquisition of resource at index i.
  Internally: half ownership of table entry showing flag=false.
*)
val permit ([@@@mkey] p: nat -> slprop) (s: sem p) (i: nat) : slprop

instance val placeless_permit p s i : placeless (permit p s i)

(** The semaphore is alive with fractional permission *)
val sem_alive
      ([@@@mkey] p: nat -> slprop)
      ([@@@mkey] s: sem p)
      (#[T.exact (`1.0R)] perm:perm)
      (max: sem_max)
  : slprop

(** Create a new semaphore with max indexed resources *)
fn new_sem (p: nat -> slprop) {| (k:nat) -> is_send (p k) |} (max: sem_max)
  requires on_range p 0 max
  returns s: sem p
  ensures sem_alive p s max

(**
  Try to acquire ANY available resource.
  Returns true on success with an existentially quantified index.
  
  Note: Current implementation is a stub that always returns false.
*)
fn try_acquire (#p: nat -> slprop) (#perm: perm) (#max: sem_max) (s: sem p)
  preserves sem_alive p s #perm max
  returns b: bool
  ensures cond b (exists* (i:nat{i < max}). permit p s i ** p i) emp

(** 
  Release resource back to the semaphore.
  Index is provided via existential from acquire.
*)
fn release (#p: nat -> slprop) (#perm: perm) (#max: sem_max) (s: sem p) (i: nat { i < max })
  preserves sem_alive p s #perm max
  requires permit p s i ** p i

(** Share semaphore permission for concurrent access *)
ghost fn share (#p: nat -> slprop) (#perm: perm) (#max: sem_max) (s: sem p)
  requires sem_alive p s #perm max
  ensures sem_alive p s #(perm /. 2.0R) max ** sem_alive p s #(perm /. 2.0R) max

(** Gather permissions back *)
[@@allow_ambiguous]
ghost fn gather (#p: nat -> slprop) (#p1 #p2: perm) (#max: sem_max) (s: sem p)
  requires sem_alive p s #p1 max ** sem_alive p s #p2 max
  ensures sem_alive p s #(p1 +. p2) max

(** 
  Try to free the semaphore. 
  Note: Current implementation is a stub that always returns false.
*)
fn try_free (#p: nat -> slprop) (#max: sem_max) (s: sem p)
  requires sem_alive p s #1.0R max
  returns b: bool
  ensures cond b (on_range p 0 max) (sem_alive p s #1.0R max)
