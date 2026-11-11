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
module Pulse.Extrinsic.WP

// Partial-correctness WP with all invariants closed at source-step boundaries.
// Atomic source steps may contain balanced core mask updates.

module L = Pulse.Extrinsic.Language
module S = PulseCore.IndirectionTheorySep
module G = Pulse.Extrinsic.Guarded

let projection (l:L.language) = S.full_mem -> GTot l.L.state
let post (l:L.language) = l.L.value -> S.slprop
let query (l:L.language) = l.L.expr & post l
let invariant (m:S.full_mem) = S.mem_invariant Pulse.Lib.GhostSet.empty m
let discard (l:L.language) (_:l.L.value) : S.slprop = S.emp

val children (l:L.language) (w:G.family (query l)) (es:list l.L.expr) : S.slprop

val children_nil (l:L.language) (w:G.family (query l))
  : Lemma (children l w [] == S.emp)

val children_cons (l:L.language) (w:G.family (query l)) (e:l.L.expr) (es:list l.L.expr)
  : Lemma (children l w (e :: es) ==
      S.star (w (e, discard l)) (children l w es))

val body (l:L.language) (physical:projection l)
  (w:G.family (query l)) : G.family (query l)

val wp_family (l:L.language) (physical:projection l) : G.family (query l)

let wp (l:L.language) (physical:projection l)
  (e:l.L.expr) (q:post l) : S.slprop =
  wp_family l physical (e, q)

val unfold_wp (l:L.language) (physical:projection l)
  (e:l.L.expr) (q:post l)
  : Lemma (
      wp l physical e q ==
      body l physical (wp_family l physical) (e, q))

val wp_value (l:L.language) (physical:projection l)
  (e:l.L.expr) (v:l.L.value) (q:post l)
  : Lemma (requires l.L.to_val e == Some v)
          (ensures wp l physical e q == q v)

val wp_step (l:L.language) (physical:projection l)
  (e:l.L.expr) (q:post l) (frame:S.slprop) (m:S.full_mem)
  : Lemma
      (requires l.L.to_val e == None /\ S.budget m > 0 /\
        S.interp (S.star (wp l physical e q) (S.star frame (invariant m))) m)
      (ensures L.reducible l e (physical m) /\
        (forall e' s' spawned.
          l.L.prim_step e (physical m) e' s' spawned ==>
          exists (m':S.full_mem).
            physical m' == s' /\
            S.level m' < S.level m /\
            S.budget m' >= S.budget m - 1 /\
            S.interp
              (S.star (wp l physical e' q)
                (S.star (children l (wp_family l physical) spawned)
                  (S.star frame (invariant m')))) m'))

let step_post (l:L.language) (physical:projection l)
  (e:l.L.expr) (q:post l) (frame:S.slprop) (m:S.full_mem) : prop =
  L.reducible l e (physical m) /\
  (forall e' s' spawned.
    l.L.prim_step e (physical m) e' s' spawned ==>
    exists (m':S.full_mem).
      physical m' == s' /\
      S.level m' < S.level m /\
      S.budget m' >= S.budget m - 1 /\
      S.interp
        (S.star (wp l physical e' q)
          (S.star (children l (wp_family l physical) spawned)
            (S.star frame (invariant m')))) m')

// Lifting covers every source transition, including nondeterministic ones.
val wp_lift (l:L.language) (physical:projection l)
  (p:S.slprop) (e:l.L.expr) (q:post l)
  (step: (frame:S.slprop -> m:S.full_mem ->
    Lemma
      (requires S.budget m > 0 /\
        S.interp (S.star p (S.star frame (invariant m))) m)
      (ensures step_post l physical e q frame m)))
  : Lemma (requires l.L.to_val e == None)
          (ensures S.implies p (wp l physical e q))

let framed_post (l:L.language) (q:post l) (frame:S.slprop) (v:l.L.value) =
  S.star (q v) frame

val wp_frame (l:L.language) (physical:projection l)
  (e:l.L.expr) (q:post l) (frame:S.slprop)
  : Lemma (S.implies (S.star (wp l physical e q) frame)
      (wp l physical e (framed_post l q frame)))

val wp_mono (l:L.language) (physical:projection l)
  (e:l.L.expr) (q q':post l)
  : Lemma
      (requires forall v. S.implies (q v) (q' v))
      (ensures S.implies (wp l physical e q) (wp l physical e q'))

noeq
type context (l:L.language) = {
  plug: l.L.expr -> l.L.expr;
  resume: l.L.value -> l.L.expr;
  values: squash (forall e v. l.L.to_val e == Some v ==> plug e == resume v);
  nonvalues: squash (forall e. l.L.to_val e == None ==> l.L.to_val (plug e) == None);
  steps: squash (forall e s e' s' spawned.
    l.L.prim_step e s e' s' spawned ==> l.L.prim_step (plug e) s (plug e') s' spawned);
  inversion: squash (forall e s next s' spawned.
    l.L.to_val e == None /\ l.L.prim_step (plug e) s next s' spawned ==>
    exists e'. next == plug e' /\ l.L.prim_step e s e' s' spawned);
}

let bind_post (l:L.language) (physical:projection l) (k:context l) (q:post l) (v:l.L.value) =
  wp l physical (k.resume v) q

val wp_bind (l:L.language) (physical:projection l) (k:context l)
  (e:l.L.expr) (q:post l)
  : Lemma (S.implies (wp l physical e (bind_post l physical k q))
      (wp l physical (k.plug e) q))
