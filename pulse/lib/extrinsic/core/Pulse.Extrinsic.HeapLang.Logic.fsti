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
module Pulse.Extrinsic.HeapLang.Logic

(** Boundary between physical PulseCore heaps and logical full memories.
    physical projects concrete memory; points_to_of lifts exclusive typed-cell
    ownership. Its observation/exposure lemmas support primitive rules.

    Native writes and arbitrary relational allocations preserve the caller's
    frame and the current mask's invariant resources. Their contracts include
    physical correspondence and exact level/budget preservation.
    world supplies initialization for uniform adequacy, not for individual
    program proofs. Program clients normally use only ownership assertions
    and exposure facts from this module. *)

module H = PulseCore.Heap
module H2 = PulseCore.Heap2
module S = PulseCore.IndirectionTheorySep
module M = Pulse.Extrinsic.HeapLang.Memory

let physical (m:S.full_mem) : GTot M.heap =
  H2.concrete (S.timeless_mem_of m)

val physical_full (m:S.full_mem) : Lemma (H.full_heap_pred (physical m))

val ghost_physical (m m':S.full_mem)
  : Lemma (requires S.is_ghost_action m m') (ensures physical m' == physical m)

val points_to_of (#a:Type0) (r:H.core_ref) (v:a) : S.slprop
val points_to (r:H.core_ref) (v:int) : S.slprop

val points_to_contents_of (#a:Type0) (r:H.core_ref) (v:a) (m:S.full_mem)
  : Lemma (requires S.interp (points_to_of r v) m)
      (ensures M.contents_of (physical m) r v)

val points_to_contents (r:H.core_ref) (v:int) (m:S.full_mem)
  : Lemma (requires S.interp (points_to r v) m)
          (ensures M.contents (physical m) r v)

val points_to_intro_of (#a:Type0) (r:H.core_ref) (v:a) (m:S.full_mem)
  : Lemma (requires H.interp (M.points_to_of r v) (physical m))
      (ensures S.interp (points_to_of r v) m)

val points_to_intro (r:H.core_ref) (v:int) (m:S.full_mem)
  : Lemma (requires H.interp (M.points_to r v) (physical m))
          (ensures S.interp (points_to r v) m)

// An atomic read can inspect a closed invariant without retaining its ownership.
val invariant_contents (r:H.core_ref) (v:int) (i:S.iref) (m:S.full_mem)
  : Lemma
      (requires S.budget m > 0 /\
        S.interp
          (S.star (S.inv i (points_to r v))
            (Pulse.Extrinsic.WP.invariant m)) m)
      (ensures M.contents (physical m) r v)

val world (h:H.full_heap u#3) (budget:nat)
  : GTot (m:S.full_mem {
      physical m == h /\ S.budget m == budget /\
      Pulse.Extrinsic.WP.invariant m == S.emp })

val install_invariant (r:H.core_ref) (v:int)
  (m:S.full_mem {
    S.budget m >= 0 /\
    S.interp (S.star (points_to r v) (Pulse.Extrinsic.WP.invariant m)) m })
  : GTot (i:S.iref & m':S.full_mem {
      physical m' == physical m /\ S.budget m' == S.budget m /\
      S.interp
        (S.star (S.inv i (points_to r v)) (Pulse.Extrinsic.WP.invariant m')) m' })

val initial_heap (v:int)
  : r:H.core_ref & h:H.full_heap u#3 { H.interp (M.points_to r v) h }

val write_memory_of (#a:Type0) (mask:S.inames) (r:H.core_ref)
  (old:FStar.Ghost.erased a) (desired:a) (frame:S.slprop)
  (m:S.full_mem { Pulse.Extrinsic.Atomic.enabled mask (points_to_of r (FStar.Ghost.reveal old)) frame m })
  : m':S.full_mem {
      S.level m' == S.level m /\ S.budget m' == S.budget m /\
      S.inames_ok mask m' /\
      M.store_of (physical m) r desired (physical m') /\
      S.interp (S.star (S.star (points_to_of r desired) frame)
        (S.mem_invariant mask m')) m' }

val write_memory (mask:S.inames) (r:H.core_ref) (old:FStar.Ghost.erased int) (desired:int) (frame:S.slprop)
  (m:S.full_mem {
    Pulse.Extrinsic.Atomic.enabled mask (points_to r old) frame m })
  : m':S.full_mem {
      S.level m' == S.level m /\ S.budget m' == S.budget m /\
      S.inames_ok mask m' /\
      M.store (physical m) r desired (physical m') /\
      S.interp (S.star (S.star (points_to r desired) frame)
        (S.mem_invariant mask m')) m' }

val exposed_lift (p:PulseCore.MemoryAlt.slprop u#0)
  : Lemma (Pulse.Extrinsic.Atomic.exposed (S.lift p) == S.later (S.lift p))

val points_to_exposed_of (#a:Type0) (r:H.core_ref) (v:a)
  : Lemma (
      S.implies (Pulse.Extrinsic.Atomic.exposed (points_to_of r v)) (points_to_of r v) /\
      S.implies (points_to_of r v) (Pulse.Extrinsic.Atomic.exposed (points_to_of r v)))

val points_to_exposed (r:H.core_ref) (v:int)
  : Lemma (
      S.implies (Pulse.Extrinsic.Atomic.exposed (points_to r v)) (points_to r v) /\
      S.implies (points_to r v) (Pulse.Extrinsic.Atomic.exposed (points_to r v)))

val allocate_memory_of (#a:Type0) (mask:S.inames) (v:a) (r:H.core_ref) (heap:M.heap) (frame:S.slprop)
  (m:S.full_mem {
    Pulse.Extrinsic.Atomic.enabled mask S.emp frame m /\
    M.allocation_of (physical m) v r heap })
  : GTot (next:S.full_mem {
      physical next == heap /\ S.level next == S.level m /\ S.budget next == S.budget m /\
      S.inames_ok mask next /\
      S.interp (S.star (S.star (points_to_of r v) frame) (S.mem_invariant mask next)) next })

val allocate_memory (mask:S.inames) (v:int) (r:H.core_ref) (heap:M.heap) (frame:S.slprop)
  (m:S.full_mem {
    Pulse.Extrinsic.Atomic.enabled mask S.emp frame m /\
    M.allocation (physical m) v r heap })
  : GTot (next:S.full_mem {
      physical next == heap /\ S.level next == S.level m /\ S.budget next == S.budget m /\
      S.inames_ok mask next /\
      S.interp (S.star (S.star (points_to r v) frame) (S.mem_invariant mask next)) next })
