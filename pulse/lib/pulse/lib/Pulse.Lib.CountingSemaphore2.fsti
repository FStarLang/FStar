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

module Pulse.Lib.CountingSemaphore2
#lang-pulse
open Pulse.Lib.Pervasives
module T = FStar.Tactics.V2
module U32 = FStar.UInt32
module Tank = Pulse.Lib.Tank

(** i copies of the resource p *)
let rec replicate (p: slprop) (i: nat) : slprop =
  match i with
  | 0 -> emp
  | _ -> p ** replicate p (i - 1)

(** Split replicate into two parts *)
ghost fn replicate_split (p: slprop) (i j: nat)
  requires replicate p (i + j)
  ensures replicate p i ** replicate p j

(** Join two replicates into one *)
ghost fn replicate_join (p: slprop) (i j: nat)
  requires replicate p i ** replicate p j
  ensures replicate p (i + j)

(** The semaphore capacity must fit in a U32 *)
let sem_max: U32.t = 0xfffffffful

(** A counting semaphore managing copies of the resources `p`. *)
val sem (p: slprop) : Type0

(** Permissions to release the semaphore. *)
val permit_tank #p (s: sem p) : Tank.tank (U32.v sem_max)

(** A permit for releasing i times. *)
let permit #p ([@@@mkey] s: sem p) (i: nat) : slprop =
  Tank.owns (permit_tank s) i

(** The semaphore is alive with fractional permission *)
val sem_alive #p ([@@@mkey] s: sem p) (#[full_default()] f:perm) : slprop

(** Create a new semaphore with n initial resources *)
fn new_sem (p: slprop) {| is_send p |} (n: U32.t)
  requires replicate p (U32.v n)
  returns s: sem p
  ensures sem_alive s
  ensures permit s (U32.v sem_max - U32.v n)

(** Create a new semaphore initialized to 0 *)
fn new_sem_0 (p: slprop) {| is_send p |}
  returns s: sem p
  ensures sem_alive s
  ensures permit s (U32.v sem_max)

(**
  Try to acquire multiple available resources with a single CAS, without waiting.
  Returns true on success.
*)
fn try_acquire_many (#p: slprop) (#f: perm) (s: sem p) (n: U32.t)
  preserves sem_alive s #f
  returns b: bool
  ensures (if b then permit s (U32.v n) ** replicate p (U32.v n) else emp)

(**
  Try to acquire an available resource, without waiting.
  Returns true on success.
*)
fn try_acquire (#p: slprop) (#f: perm) (s: sem p)
  preserves sem_alive s #f
  returns b: bool
  ensures (if b then permit s 1 ** p else emp)

(** Release resource to the semaphore. *)
fn release (#p: slprop) (#f: perm) (s: sem p)
  preserves sem_alive s #f
  requires permit s 1 ** p

(** Share semaphore permission for concurrent access *)
ghost fn share (#p: slprop) (#f: perm) (s: sem p)
  requires sem_alive s #f
  ensures sem_alive s #(f /. 2.0R) ** sem_alive s #(f /. 2.0R)

(** Gather permissions back *)
[@@allow_ambiguous]
ghost fn gather (#p: slprop) (#p1 #p2: perm) (s: sem p)
  requires sem_alive s #p1 ** sem_alive s #p2
  ensures sem_alive s #(p1 +. p2)

(** Free the semaphore. *)
fn free (#p: slprop) (s: sem p)
  requires sem_alive s
