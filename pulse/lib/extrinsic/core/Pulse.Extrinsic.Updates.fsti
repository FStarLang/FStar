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
module Pulse.Extrinsic.Updates

(** Framed ghost mask-update judgments over the same logical memories as WP.
    A result preserves physical state and budget, may lower logical level,
    and establishes ownership and invariant consistency at the output mask.
    These are the semantic judgments underlying FancyUpdates.fupd, which
    internalizes them as owned assertions.

    Entailment, transitivity, frame, and existential rules compose updates.
    Open/close, allocation, and paid later elimination reuse native machinery.
    [bind_wp] only admits a closed-to-closed update before a NON-VALUE: the
    unchanged strict WP value equation has nowhere to execute a ghost update.
    HeapLang.FancyProof provides the update-closed value/continuation rules. *)

module L = Pulse.Extrinsic.Language
module W = Pulse.Extrinsic.WP
module S = PulseCore.IndirectionTheorySep
module A = Pulse.Extrinsic.Atomic

let enabled (mask:S.inames) (p frame:S.slprop) (m:S.full_mem) =
  S.budget m >= 0 /\ S.inames_ok mask m /\
  S.interp (S.star (S.star p frame) (S.mem_invariant mask m)) m

let result (l:L.language) (physical:W.projection l) (mask:S.inames)
  (q frame:S.slprop) (m next:S.full_mem) =
  physical next == physical m /\ S.level next <= S.level m /\
  S.budget next == S.budget m /\ enabled mask q frame next

val hoare (l:L.language) (physical:W.projection l)
  (before after:S.inames) (p q:S.slprop) : prop

val lift (l:L.language) (physical:W.projection l)
  (before after:S.inames) (p q:S.slprop)
  (step:(f:S.slprop -> m:S.full_mem ->
    Lemma (requires enabled before p f m)
      (ensures exists (next:S.full_mem). result l physical after q f m next)))
  : Lemma (hoare l physical before after p q)

val entails (l:L.language) (physical:W.projection l) (mask:S.inames) (p q:S.slprop)
  : Lemma (requires S.implies p q) (ensures hoare l physical mask mask p q)
val false_pre (l:L.language) (physical:W.projection l) (before after:S.inames) (q:S.slprop)
  : Lemma (hoare l physical before after (S.pure False) q)
val trans (l:L.language) (physical:W.projection l)
  (before middle after:S.inames) (p q r:S.slprop)
  : Lemma (requires hoare l physical before middle p q /\ hoare l physical middle after q r)
      (ensures hoare l physical before after p r)
val frame (l:L.language) (physical:W.projection l)
  (before after:S.inames) (p q f:S.slprop)
  : Lemma (requires hoare l physical before after p q)
      (ensures hoare l physical before after (S.star p f) (S.star q f))
val exists_pre (#a:Type) (l:L.language) (physical:W.projection l)
  (before after:S.inames) (p:a -> S.slprop) (q:S.slprop)
  : Lemma (requires forall x. hoare l physical before after (p x) q)
      (ensures hoare l physical before after (S.op_exists_Star p) q)
val pure_pre (l:L.language) (physical:W.projection l)
  (before after:S.inames) (p q:S.slprop) (fact:prop)
  (proof:(unit -> Lemma (requires fact) (ensures hoare l physical before after p q)))
  : Lemma (hoare l physical before after (S.star p (S.pure fact)) q)
val open_invariant (l:L.language) (physical:W.projection l)
  (mask:S.inames) (i:S.iref{not (S.mem_inv mask i)}) (p:S.slprop)
  : Lemma (hoare l physical mask (S.add_inv mask i)
      (S.inv i p) (S.star (S.inv i p) (A.exposed p)))
val close_invariant (l:L.language) (physical:W.projection l)
  (mask:S.inames) (i:S.iref{not (S.mem_inv mask i)}) (p:S.slprop)
  : Lemma (hoare l physical (S.add_inv mask i) mask
      (S.star (S.inv i p) (A.exposed p)) (S.inv i p))

let allocated (p:S.slprop) = S.op_exists_Star (fun (i:S.iref) -> S.inv i p)

val allocate (l:L.language) (physical:W.projection l) (p:S.slprop)
  (ghost:(m:S.full_mem -> next:S.full_mem ->
    Lemma (requires S.is_ghost_action m next) (ensures physical next == physical m)))
  : Lemma (hoare l physical Pulse.Lib.GhostSet.empty Pulse.Lib.GhostSet.empty p (allocated p))

val later_elim (l:L.language) (physical:W.projection l) (mask:S.inames) (p:S.slprop)
  (ghost:(m:S.full_mem -> next:S.full_mem ->
    Lemma (requires S.is_ghost_action m next) (ensures physical next == physical m)))
  : Lemma (hoare l physical mask mask (S.star (S.later p) (S.later_credit 1)) p)

val apply (l:L.language) (physical:W.projection l)
  (before after:S.inames) (p q f:S.slprop) (m:S.full_mem)
  : Lemma (requires hoare l physical before after p q /\ enabled before p f m)
      (ensures exists (next:S.full_mem). result l physical after q f m next)

val bind_wp (l:L.language) (physical:W.projection l)
  (p mid:S.slprop) (e:l.L.expr) (q:W.post l)
  : Lemma
      (requires l.L.to_val e == None /\
        hoare l physical Pulse.Lib.GhostSet.empty Pulse.Lib.GhostSet.empty p mid /\
        S.implies mid (W.wp l physical e q))
      (ensures S.implies p (W.wp l physical e q))
