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
module Pulse.Extrinsic.HeapLang.Rules

open Pulse.Extrinsic.HeapLang
module E = Pulse.Extrinsic.HeapLang.Semantics
module M = Pulse.Extrinsic.HeapLang.Logic
module W = Pulse.Extrinsic.WP
module R = Pulse.Extrinsic.Rules
module S = PulseCore.IndirectionTheorySep

let wp (#t:ty) (e:expr [] t) (q:W.post E.language) =
  W.wp E.language M.physical (E.Pack t e) q

let children (es:list E.thread) =
  W.children E.language (W.wp_family E.language M.physical) (E.pack_threads es)

let hoare (#t:ty) (p:S.slprop) (e:expr [] t) (q:W.post E.language) =
  S.implies p (wp e q)

let apply_frame (p q frame:S.slprop) (m:S.mem)
  : Lemma
      (requires S.level m > 0 /\ S.implies p q /\ S.interp (S.star p frame) m)
      (ensures S.interp (S.star q frame) m)
  = R.entails_refl frame;
    R.entails_star p q frame frame;
    S.elim_implies (S.star p frame) (S.star q frame) m

let wp_transition (#t:ty) (p:S.slprop) (e next:expr [] t)
  (spawned:list E.thread) (q:W.post E.language)
  (step: (m:S.full_mem ->
    Lemma
      (requires S.budget m > 0 /\ S.interp (S.star p (W.invariant m)) m)
      (ensures E.transition e next spawned (M.physical m))))
  : Lemma
      (requires to_val e == None /\ S.implies p (S.star (wp next q) (children spawned)))
      (ensures hoare p e q)
  = R.wp_readonly E.language M.physical p (E.Pack t e) q (fun frame m ->
      S.sep_laws ();
      S.destruct_star_l (S.star p (W.invariant m)) frame m;
      step m;
      E.pack_transition e next spawned (M.physical m);
      apply_frame p (S.star (wp next q) (children spawned))
        (S.star frame (W.invariant m)) m)

let wp_value (#t:ty) (p:S.slprop) (v:value t) (q:W.post E.language)
  : Lemma
      (requires S.implies p (q (E.PackValue t v)))
      (ensures hoare p (Val v) q)
  = W.wp_value E.language M.physical (E.Pack t (Val v)) (E.PackValue t v) q

let wp_pure_later (#t:ty) (p:S.slprop) (e next:expr [] t) (q:W.post E.language)
  (step:(h:Pulse.Extrinsic.HeapLang.Memory.heap ->
    Lemma (E.transition e next [] h)))
  : Lemma
      (requires to_val e == None /\ S.implies p (S.later (wp next q)))
      (ensures hoare p e q)
  = S.sep_laws ();
    W.children_nil E.language (W.wp_family E.language M.physical);
    W.wp_lift E.language M.physical p (E.Pack t e) q (fun f m ->
      apply_frame p (S.later (wp next q)) (S.star f (W.invariant m)) m;
      R.age_later_resources (wp next q) f m;
      M.ghost_physical m (S.age_mem m);
      step (M.physical m);
      E.pack_transition e next [] (M.physical m);
      introduce forall e' s' spawned.
        E.packed_step (E.Pack t e) (M.physical m) e' s' spawned ==>
        (exists (m':S.full_mem).
          M.physical m' == s' /\ S.level m' < S.level m /\
          S.budget m' >= S.budget m - 1 /\
          S.interp (S.star (W.wp E.language M.physical e' q)
            (S.star (W.children E.language (W.wp_family E.language M.physical) spawned)
              (S.star f (W.invariant m')))) m')
      with (
        introduce E.packed_step (E.Pack t e) (M.physical m) e' s' spawned ==>
          (exists (m':S.full_mem).
            M.physical m' == s' /\ S.level m' < S.level m /\
            S.budget m' >= S.budget m - 1 /\
            S.interp (S.star (W.wp E.language M.physical e' q)
              (S.star (W.children E.language (W.wp_family E.language M.physical) spawned)
                (S.star f (W.invariant m')))) m')
        with (
          introduce exists (m':S.full_mem).
            M.physical m' == s' /\ S.level m' < S.level m /\
            S.budget m' >= S.budget m - 1 /\
            S.interp (S.star (W.wp E.language M.physical e' q)
              (S.star (W.children E.language (W.wp_family E.language M.physical) spawned)
                (S.star f (W.invariant m')))) m'
          with (S.age_mem m) and ())))

let wp_load_inv (r:PulseCore.Heap.core_ref) (v:int) (i:S.iref) (q:W.post E.language)
  : Lemma
      (requires S.implies (S.inv i (M.points_to r v)) (q (E.PackValue TInt v)))
      (ensures hoare (S.inv i (M.points_to r v)) (Load (Val r)) q)
  = S.sep_laws ();
    W.children_nil E.language (W.wp_family E.language M.physical);
    wp_value (S.inv i (M.points_to r v)) v q;
    wp_transition (S.inv i (M.points_to r v)) (Load (Val r)) (Val v) [] q (fun m ->
      M.invariant_contents r v i m;
      E.read_transition r v (M.physical m))

let wp_sequence_value (#t:ty) (p:S.slprop) (e:expr [] t) (q:W.post E.language)
  : Lemma (requires hoare p e q)
          (ensures hoare p (Seq (Val ()) e) q)
  = S.sep_laws ();
    W.children_nil E.language (W.wp_family E.language M.physical);
    wp_transition p (Seq (Val ()) e) e [] q (fun m -> E.sequence_transition e (M.physical m))

let wp_beta (#a #b:ty) (p:S.slprop) (v:value a) (body:expr [a] b) (q:W.post E.language)
  : Lemma (requires hoare p (substitute v body) q)
          (ensures hoare p (Let (Val v) body) q)
  = S.sep_laws ();
    W.children_nil E.language (W.wp_family E.language M.physical);
    wp_transition p (Let (Val v) body) (substitute v body) [] q
      (fun m -> E.beta_transition v body (M.physical m))

let wp_fork (parent child:S.slprop) (e:E.thread) (q:W.post E.language)
  : Lemma
      (requires S.implies parent (q (E.PackValue TUnit ())) /\
        hoare child e (W.discard E.language))
      (ensures hoare (S.star parent child) (Fork e) q)
  = S.sep_laws ();
    wp_value parent () q;
    W.children_cons E.language (W.wp_family E.language M.physical) (E.Pack TUnit e) [];
    W.children_nil E.language (W.wp_family E.language M.physical);
    R.entails_star parent (wp (Val ()) q) child (wp e (W.discard E.language));
    wp_transition (S.star parent child) (Fork e) (Val ()) [e] q
      (fun m -> E.fork_transition e (M.physical m))
