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
module Pulse.Extrinsic.AtomicLogic

(** Masked atomic judgments about source expressions, not native programs.
    Every step must return a value, spawn no threads, and restore the mask's
    resources. This supports consequence and existential proofs even when
    there is no single chosen native execution witnessing the whole proof.

    Atomic proofs preserve budget: the source-step charge is reserved for
    embedding into WP. [to_wp_later] uses that charge to eliminate one later
    from the postcondition, including arbitrary higher-order ownership.
    [invariant] brackets one such source step; it cannot bracket an ordinary
    multi-step Hoare triple. See HeapLang.AtomicUpdate for the distinct
    retry/abort/commit protocol used to specify multi-step implementations. *)

module L = Pulse.Extrinsic.Language
module W = Pulse.Extrinsic.WP
module R = Pulse.Extrinsic.Rules
module A = Pulse.Extrinsic.Atomic
module S = PulseCore.IndirectionTheorySep

// Semantic contracts used only when implementing primitive rules.
let result (l:L.language) (physical:W.projection l) (mask:S.inames)
  (q:W.post l) (f:S.slprop) (m:S.full_mem)
  (e':l.L.expr) (s':l.L.state) (spawned:list l.L.expr) : prop =
  exists v (next:S.full_mem).
    l.L.to_val e' == Some v /\ spawned == [] /\ physical next == s' /\
    S.level next <= S.level m /\ S.budget next >= S.budget m /\
    S.inames_ok mask next /\
    S.interp (S.star (S.star (q v) f) (S.mem_invariant mask next)) next

let step_post (l:L.language) (physical:W.projection l) (mask:S.inames)
  (e:l.L.expr) (q:W.post l) (f:S.slprop) (m:S.full_mem) : prop =
  L.reducible l e (physical m) /\
  (forall e' s' spawned. l.L.prim_step e (physical m) e' s' spawned ==>
    result l physical mask q f m e' s' spawned)

// A source judgment: every reduction returns a value and restores this mask.
val hoare (l:L.language) (physical:W.projection l) (mask:S.inames)
  (p:S.slprop) (e:l.L.expr) (q:W.post l) : prop

val nonvalue (l:L.language) (physical:W.projection l) (mask:S.inames)
  (p:S.slprop) (e:l.L.expr) (q:W.post l)
  : Lemma (requires hoare l physical mask p e q) (ensures l.L.to_val e == None)

val consequence (l:L.language) (physical:W.projection l) (mask:S.inames)
  (p p':S.slprop) (e:l.L.expr) (q q':W.post l)
  : Lemma
      (requires hoare l physical mask p e q /\ S.implies p' p /\
        (forall v. S.implies (q v) (q' v)))
      (ensures hoare l physical mask p' e q')

val frame (l:L.language) (physical:W.projection l) (mask:S.inames)
  (p:S.slprop) (e:l.L.expr) (q:W.post l) (f:S.slprop)
  : Lemma
      (requires hoare l physical mask p e q)
      (ensures hoare l physical mask (S.star p f) e (W.framed_post l q f))

val exists_pre (#a:Type0) (l:L.language) (physical:W.projection l) (mask:S.inames)
  (p:a -> S.slprop) (e:l.L.expr) (q:W.post l)
  : Lemma
      (requires l.L.to_val e == None /\ (forall x. hoare l physical mask (p x) e q))
      (ensures hoare l physical mask (S.op_exists_Star p) e q)

val invariant (l:L.language) (physical:W.projection l)
  (mask:S.inames) (i:S.iref{not (S.mem_inv mask i)})
  (p pre:S.slprop) (e:l.L.expr) (post:W.post l)
  : Lemma
      (requires hoare l physical (S.add_inv mask i)
        (S.star (A.exposed p) pre) e (A.exposed_post p post))
      (ensures hoare l physical mask (S.star (S.inv i p) pre) e
        (A.protected_post i p post))

let later_post (l:L.language) (q:W.post l) (v:l.L.value) = S.later (q v)

val to_wp_later (l:L.language) (physical:W.projection l)
  (p:S.slprop) (e:l.L.expr) (q:W.post l)
  : Lemma
      (requires R.age_stable l physical /\
        hoare l physical Pulse.Lib.GhostSet.empty p e (later_post l q))
      (ensures R.hoare l physical p e q)

val to_wp (l:L.language) (physical:W.projection l)
  (p:S.slprop) (e:l.L.expr) (q:W.post l)
  : Lemma
      (requires R.age_stable l physical /\
        hoare l physical Pulse.Lib.GhostSet.empty p e q)
      (ensures R.hoare l physical p e q)

val lift (l:L.language) (physical:W.projection l) (mask:S.inames)
  (p:S.slprop) (e:l.L.expr) (q:W.post l)
  (proof:(f:S.slprop -> m:S.full_mem ->
    Lemma (requires A.enabled mask p f m)
      (ensures step_post l physical mask e q f m)))
  : Lemma (requires l.L.to_val e == None)
      (ensures hoare l physical mask p e q)

val updates (l:L.language) (physical:W.projection l)
  (outer inner:S.inames) (p mid:S.slprop) (e:l.L.expr) (q post:W.post l)
  : Lemma
      (requires Pulse.Extrinsic.Updates.hoare l physical outer inner p mid /\
        hoare l physical inner mid e q /\
        (forall v. Pulse.Extrinsic.Updates.hoare l physical inner outer (q v) (post v)))
      (ensures hoare l physical outer p e post)
