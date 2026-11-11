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
module Pulse.Extrinsic.Ghost
friend Pulse.Extrinsic.HeapLang.Proof
friend PulseCore.IndirectionTheoryActions
friend PulseCore.IndirectionTheorySep
friend PulseCore.MemoryAlt
friend PulseCore.BaseHeapSig
friend PulseCore.Heap2

open FStar.PCM
module S = PulseCore.IndirectionTheorySep
module IA = PulseCore.IndirectionTheoryActions
module PM = PulseCore.MemoryAlt
module H = PulseCore.Heap
module H2 = PulseCore.Heap2
module C = Pulse.Extrinsic.HeapLang.Logic
module E = Pulse.Extrinsic.HeapLang.Semantics
module P = Pulse.Extrinsic.HeapLang.Proof
module U = Pulse.Extrinsic.Updates
module R = Pulse.Extrinsic.Rules
module Up = FStar.Universe
module PC = FStar.Universe.PCM
module K = PulseCore.KnotInstantiation

let base (#a:Type0) (pcm:pcm a) (g:name) (x:a) =
  PM.ghost_pts_to #(Up.raise_t u#0 u#3 a) #(PC.raise u#0 u#3 pcm)
    g (Up.raise_val u#0 u#3 x)
let own #a pcm g x = S.lift (base pcm g x)

let memory_update (#a:Type0) (mask:S.inames)
  (pre:PM.slprop u#0) (post:a -> PM.slprop u#0) (out:S.slprop)
  (action:PM.pst_ghost_action_except a pre post)
  : Lemma
      (requires forall x. S.implies (S.lift (post x)) out)
      (ensures P.update mask mask (S.lift pre) out)
  = S.sep_laws ();
    U.lift E.language C.physical mask mask (S.lift pre) out (fun f m ->
      let act = IA.lift_mem_action #a #true #mask action in
      let (| bf, restore |) = IA.pin_frame pre (S.star f (S.mem_invariant mask m)) m in
      let x, bn = action bf (S.timeless_mem_of m) in
      let v, next = act f m in
      assert (next == S.update_timeless_mem m bn);
      K.level_pack (S.level m) { (S.unpack m) with K.timeless_heap = bn };
      K.credits_pack (S.level m) { (S.unpack m) with K.timeless_heap = bn };
      C.ghost_physical m next;
      let tail = S.star f (S.mem_invariant mask next) in
      R.entails_refl tail;
      R.entails_star (S.lift (post v)) out tail tail;
      S.elim_implies (S.star (S.lift (post v)) tail) (S.star out tail) next;
      assert (U.enabled mask out f next);
      introduce exists (next:S.full_mem).
        U.result E.language C.physical mask out f m next
      with next and ())

let alloc #a mask pcm x =
  S.lift_emp_eq ();
  introduce forall (g:name). S.implies (own pcm g x) (allocated pcm x)
  with (
    S.implies_intro (own pcm g x) (allocated pcm x) (fun h ->
      introduce exists (g':name). own pcm g' x h with g and ()));
  memory_update mask PM.emp (fun g -> base pcm g x) (allocated pcm x)
    (PM.ghost_alloc #(Up.raise_t u#0 u#3 a) #(PC.raise u#0 u#3 pcm)
      (Up.raise_val u#0 u#3 x))

let write #a mask pcm g x y upd =
  R.entails_refl (own pcm g y);
  memory_update mask (base pcm g x) (fun (_:unit) -> base pcm g y) (own pcm g y)
    (PM.ghost_write g (Up.raise_val u#0 u#3 x) (Up.raise_val u#0 u#3 y)
      (PC.raise_frame_preserving_upd u#0 u#3 upd))

let split #a pcm g x y =
  let xx = Up.raise_val u#0 u#3 x in
  let yy = Up.raise_val u#0 u#3 y in
  H2.ghost_pts_to_compatible_equiv #(Up.raise_t u#0 u#3 a) #(PC.raise u#0 u#3 pcm) g xx yy;
  H2.slprop_extensionality (H2.star (base pcm g x) (base pcm g y))
    (base pcm g (op pcm x y));
  S.lift_star_eq (base pcm g x) (base pcm g y)

let compatible #a pcm g x y =
  S.implies_intro (S.star (own pcm g x) (own pcm g y))
    (S.pure (composable pcm x y)) (fun h ->
      S.lift_star_eq (base pcm g x) (base pcm g y);
      H2.lift_star PulseCore.Tags.GHOST
        (H.pts_to #(Up.raise_t u#0 u#3 a) #(PC.raise u#0 u#3 pcm) g (Up.raise_val u#0 u#3 x))
        (H.pts_to #(Up.raise_t u#0 u#3 a) #(PC.raise u#0 u#3 pcm) g (Up.raise_val u#0 u#3 y));
      H.pts_to_compatible #(Up.raise_t u#0 u#3 a) #(PC.raise u#0 u#3 pcm)
        g (Up.raise_val u#0 u#3 x) (Up.raise_val u#0 u#3 y)
        (H2.ghost (K.timeless_heap_of h)))

let exposed #a pcm g x =
  C.exposed_lift (base pcm g x);
  S.timeless_lift (base pcm g x);
  R.entails_later (own pcm g x)
