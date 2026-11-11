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
module Pulse.Extrinsic.Atomic

module L = Pulse.Extrinsic.Language
module W = Pulse.Extrinsic.WP
module R = Pulse.Extrinsic.Rules
module S = PulseCore.IndirectionTheorySep
module M = PulseCore.Masks
module IA = PulseCore.IndirectionTheoryActions
module O = PulseCore.Observability

let enabled (mask:S.inames) (p frame:S.slprop) (m:S.full_mem) : prop =
  S.budget m > 0 /\ S.inames_ok mask m /\
  S.interp (S.star (S.star p frame) (S.mem_invariant mask m)) m

// Expose the existing core action semantics for correspondence proofs.
val run (#a:Type0) (#o:O.observability) (#before #after:S.inames)
  (#p:S.slprop) (#q:a -> S.slprop)
  (f:M.action a o before after p q) (frame:S.slprop)
  (m:S.full_mem {
    S.budget m >= 0 /\ (o == O.Observable ==> S.budget m > 0) /\
    S.inames_ok before m /\
    S.interp (S.star (S.star p frame) (S.mem_invariant before m)) m })
  : result:(a & S.full_mem) {
    let x, m' = result in
    S.budget m' >= S.budget m - 1 /\
    (o == O.Neutral ==> S.is_ghost_action m m' /\ S.budget m' == S.budget m) /\
    S.inames_ok after m' /\
    S.interp (S.star (S.star (q x) frame) (S.mem_invariant after m')) m' }

val native (#a:Type0) (#mask:S.inames) (#p:S.slprop) (#q:a -> S.slprop)
  (f:IA.act a mask p q) : M.action a O.Observable mask mask p q

val run_native (#a:Type0) (#mask:S.inames) (#p:S.slprop) (#q:a -> S.slprop)
  (f:IA.act a mask p q) (frame:S.slprop) (m:S.full_mem{enabled mask p frame m})
  : Lemma (let _ = S.sep_laws () in run (native f) frame m == f frame m)

// The action must cover every source reduction, not merely produce one execution.
// Level-preserving actions leave room to age once; existing credit-consuming
// ghost proofs may already have decreased the level.
let realizes (#a:Type0) (l:L.language) (physical:W.projection l)
  (e:l.L.expr) (decode:a -> l.L.value) (mask:S.inames)
  (p:S.slprop) (q:a -> S.slprop) (f:M.action a O.Observable mask mask p q) : prop =
  forall frame (m:S.full_mem). enabled mask p frame m ==>
    (let x, m' = run f frame m in
     S.level m' <= S.level m /\
     (S.level m' == S.level m ==> S.budget m' >= S.budget m) /\
     L.reducible l e (physical m) /\
     (forall e' s' spawned.
       l.L.prim_step e (physical m) e' s' spawned ==>
       l.L.to_val e' == Some (decode x) /\ s' == physical m' /\ spawned == []))

let exposed (p:S.slprop) = S.somewhere (S.later p)
let exposed_post (#a:Type0) (p:S.slprop) (q:a -> S.slprop) (x:a) =
  S.star (exposed p) (q x)
let protected_post (#a:Type0) (i:S.iref) (p:S.slprop) (q:a -> S.slprop) (x:a) =
  S.star (S.inv i p) (q x)

// Open/close are PulseCore.Masks actions, not new invariant axioms.
val open_invariant (mask:S.inames) (i:S.iref{not (S.mem_inv mask i)}) (p:S.slprop)
  : M.action (FStar.Ghost.erased unit) O.Neutral mask (S.add_inv mask i)
      (S.inv i p) (fun _ -> S.star (S.inv i p) (exposed p))
val close_invariant (mask:S.inames) (i:S.iref{not (S.mem_inv mask i)}) (p:S.slprop)
  : M.action (FStar.Ghost.erased unit) O.Neutral (S.add_inv mask i) mask
      (S.star (S.inv i p) (exposed p)) (fun _ -> S.inv i p)

val with_invariant (#a:Type0) (mask:S.inames) (i:S.iref{not (S.mem_inv mask i)})
  (p pre:S.slprop) (post:a -> S.slprop)
  (f:M.action a O.Observable (S.add_inv mask i) (S.add_inv mask i)
    (S.star (exposed p) pre) (exposed_post p post))
  : M.action a O.Observable mask mask (S.star (S.inv i p) pre) (protected_post i p post)

val open_unchanged (mask:S.inames) (i:S.iref{not (S.mem_inv mask i)})
  (p frame:S.slprop) (m:S.full_mem{enabled mask (S.inv i p) frame m})
  : Lemma ((run (open_invariant mask i p) frame m)._2 == m)

val close_unchanged (mask:S.inames) (i:S.iref{not (S.mem_inv mask i)})
  (p frame:S.slprop) (m:S.full_mem {
    S.budget m >= 0 /\ S.inames_ok (S.add_inv mask i) m /\
    S.interp (S.star (S.star (S.star (S.inv i p) (exposed p)) frame)
      (S.mem_invariant (S.add_inv mask i) m)) m })
  : Lemma ((run (close_invariant mask i p) frame m)._2 == m)

val realizes_with_invariant (#a:Type0) (l:L.language) (physical:W.projection l)
  (e:l.L.expr) (decode:a -> l.L.value)
  (mask:S.inames) (i:S.iref{not (S.mem_inv mask i)})
  (p pre:S.slprop) (post:a -> S.slprop)
  (f:M.action a O.Observable (S.add_inv mask i) (S.add_inv mask i)
    (S.star (exposed p) pre) (exposed_post p post))
  : Lemma
      (requires realizes l physical e decode (S.add_inv mask i)
        (S.star (exposed p) pre) (exposed_post p post) f)
      (ensures realizes l physical e decode mask
        (S.star (S.inv i p) pre) (protected_post i p post)
        (with_invariant mask i p pre post f))

val wp_atomic (l:L.language) (physical:W.projection l)
  (e:l.L.expr) (p:S.slprop) (q:W.post l)
  (f:M.action l.L.value O.Observable Pulse.Lib.GhostSet.empty Pulse.Lib.GhostSet.empty p q)
  : Lemma
      (requires l.L.to_val e == None /\ R.age_stable l physical /\
        realizes l physical e (fun v -> v) Pulse.Lib.GhostSet.empty p q f)
      (ensures R.hoare l physical p e q)

val allocate_invariant (p frame:S.slprop)
  (m:S.full_mem {
    S.budget m >= 0 /\ S.interp (S.star p (S.star frame (W.invariant m))) m })
  : i:S.iref & m':S.full_mem {
      S.is_ghost_action m m' /\ S.level m' == S.level m /\ S.budget m' == S.budget m /\
      S.interp (S.star (S.inv i p) (S.star frame (W.invariant m'))) m' }
