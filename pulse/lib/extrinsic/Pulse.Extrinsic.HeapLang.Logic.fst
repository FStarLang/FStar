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
friend PulseCore.Heap2
friend PulseCore.BaseHeapSig
friend PulseCore.IndirectionTheorySep
friend PulseCore.Heap
friend PulseCore.MemoryAlt
friend PulseCore.IndirectionTheoryActions

module H = PulseCore.Heap
module H2 = PulseCore.Heap2
module S = PulseCore.IndirectionTheorySep
module M = Pulse.Extrinsic.HeapLang.Memory
module W = Pulse.Extrinsic.WP
module GS = Pulse.Lib.GhostSet
module IA = PulseCore.IndirectionTheoryActions
module PM = PulseCore.MemoryAlt
module A = Pulse.Extrinsic.Atomic
module R = Pulse.Extrinsic.Rules
module K = PulseCore.KnotInstantiation

let ghost_physical m m' = ()

let points_to r v =
  S.lift (H2.pts_to #M.cell_value #M.cell_pcm r (M.Full v))

let points_to_base (r:H.core_ref) (v:int) (m:S.full_mem)
  : Lemma (requires S.interp (points_to r v) m)
          (ensures H.interp (M.points_to r v) (physical m))
  = S.lift_eq (H2.pts_to #M.cell_value #M.cell_pcm r (M.Full v))

let points_to_contents r v m =
  points_to_base r v m;
  M.points_to_contents r v (physical m)

let points_to_intro r v m =
  S.lift_eq (H2.pts_to #M.cell_value #M.cell_pcm r (M.Full v))

let invariant_contents r v i m =
  let p = points_to r v in
  S.sep_laws ();
  S.destruct_star_l (S.inv i p) (W.invariant m) m;
  S.inames_ok_single i p m;
  S.mem_invariant_equiv GS.empty m i;
  S.destruct_star_l
    (S.star (S.read_inv i m) (S.inv i p))
    (S.mem_invariant (S.add_inv GS.empty i) m) m;
  S.read_inv_elim i m p;
  assert_norm (S.somewhere (S.later p) ==
    S.op_exists_Star (fun loc -> S.on loc (S.later p)));
  S.interp_exists (fun loc -> S.on loc (S.later p));
  eliminate exists loc. S.interp (S.on loc (S.later p)) m with (
    S.on_later_eq loc p;
    S.on_lift_eq loc (H2.pts_to #M.cell_value #M.cell_pcm r (M.Full v));
    S.timeless_lift (H2.pts_to #M.cell_value #M.cell_pcm r (M.Full v));
    S.elim_implies (S.later p) p m;
    points_to_contents r v m
  )

let world h budget =
  let base = S.empty (budget + 1) Pulse.Lib.Loc.dummy_loc in
  let m = S.update_timeless_mem base { H2.concrete = h; H2.ghost = H.empty_heap } in
  assert (H.full_heap_pred H.empty_heap);
  assert (S.is_full m);
  S.hogs_invariant__congr GS.empty m (S.some_fresh_addr m) 0;
  assert_norm (S.hogs_invariant_ GS.empty m 0 == S.emp);
  m

let install_invariant r v m =
  S.sep_laws ();
  let (| i, m' |) = A.allocate_invariant (points_to r v) S.emp m in
  ghost_physical m m';
  (| i, m' |)

let initial_heap v =
  assert (H.full_heap_pred H.empty_heap);
  let (| r, h |) = M.allocate v H.empty_heap in
  (| r, h |)

let write_core (mask:S.inames) (r:H.core_ref) (old:FStar.Ghost.erased int) (desired:int)
  : IA.act unit mask (points_to r old) (fun _ -> points_to r desired)
  = IA.lift_mem_action #unit #false #mask
      (PM.upd_gen #M.cell_value #M.cell_pcm r (M.Full old) (M.Full desired) (M.replace old desired))

let write_correspondence (mask:S.inames) (r:H.core_ref) (old:FStar.Ghost.erased int) (desired:int) (frame:S.slprop)
  (m:S.full_mem{Pulse.Extrinsic.Atomic.enabled mask (points_to r old) frame m})
  : Lemma (
      let _, next = write_core mask r old desired frame m in
      S.level next == S.level m /\ S.budget next == S.budget m /\
      M.store (physical m) r desired (physical next))
  =
  S.sep_laws ();
  S.destruct_star_l (points_to r old) (S.star frame (S.mem_invariant mask m)) m;
  points_to_base r old m;
  points_to_contents r old m;
  let update = M.replace old desired in
  let f = PM.upd_gen #M.cell_value #M.cell_pcm r (M.Full old) (M.Full desired) update in
  let (| base_frame, restore |) = IA.pin_frame
    (PM.pts_to #M.cell_value #M.cell_pcm r (M.Full old))
    (S.star frame (S.mem_invariant mask m)) m in
  let _, base_next = f base_frame (S.timeless_mem_of m) in
  let _, next = write_core mask r old desired frame m in
  S.destruct_star_l (points_to r desired) (S.star frame (S.mem_invariant mask next)) next;
  assert (next == S.update_timeless_mem m base_next);
  H.upd_gen_modifies r (M.Full old) (M.Full desired) update (physical m);
  let (| _, raw_next |) = H.upd_gen_action r (M.Full old) (M.Full desired) update (physical m) in
  assert (physical next == raw_next);
  points_to_contents r desired next

let write_memory mask r old desired frame m =
  write_correspondence mask r old desired frame m;
  let _, next = write_core mask r old desired frame m in
  next

let bit_base (r:H.core_ref) =
  H2.h_exists (fun (n:bit) -> H2.pts_to #M.cell_value #M.cell_pcm r (M.Full n))

let bit_cell r = S.lift (bit_base r)

let bit_cell_unfold r =
  K.mem_pred_ext (bit_cell r) (S.op_exists_Star (bit_point r)) (fun h ->
    assert_norm (bit_cell r h == (exists (n:bit). points_to r n h));
    assert_norm (S.op_exists_Star (bit_point r) h == (exists (n:bit). points_to r n h)))

let bit_cell_intro r n =
  bit_cell_unfold r;
  S.implies_intro (points_to r n) (bit_cell r) (fun h ->
    introduce exists (v:bit). points_to r v h with n and ())

let exposed_lift (p:PM.slprop u#0)
  : Lemma (A.exposed (S.lift p) == S.later (S.lift p))
  = K.mem_pred_ext (A.exposed (S.lift p)) (S.later (S.lift p)) (fun h ->
      assert_norm (A.exposed (S.lift p) h ==
        (exists loc. S.on loc (S.later (S.lift p)) h));
      introduce forall loc. S.on loc (S.later (S.lift p)) == S.later (S.lift p)
      with (S.on_later_eq loc (S.lift p); S.on_lift_eq loc p);
      introduce S.later (S.lift p) h ==> A.exposed (S.lift p) h with (
        introduce exists loc. S.on loc (S.later (S.lift p)) h
        with Pulse.Lib.Loc.dummy_loc and ()
      ))

let bit_cell_exposed r =
  exposed_lift (bit_base r);
  S.timeless_lift (bit_base r);
  S.implies_intro (bit_cell r) (A.exposed (bit_cell r)) (fun _ -> S.reveal_slprop_ok ())

let bit_cell_witness mask r frame m =
  S.sep_laws ();
  bit_cell_exposed r;
  bit_cell_unfold r;
  let rest = S.star frame (S.mem_invariant mask m) in
  R.entails_refl rest;
  R.entails_star (A.exposed (bit_cell r)) (bit_cell r) rest rest;
  S.elim_implies (S.star (A.exposed (bit_cell r)) rest) (S.star (bit_cell r) rest) m;
  let n, next = IA.witness_exists #mask (bit_point r) frame m in
  assert_norm (next == m);
  n

let bit_invariant_contents r i m =
  S.sep_laws ();
  S.inames_ok_empty m;
  A.open_unchanged GS.empty i (bit_cell r) S.emp m;
  let _, opened = A.run (A.open_invariant GS.empty i (bit_cell r)) S.emp m in
  let n = bit_cell_witness (S.add_inv GS.empty i) r (S.inv i (bit_cell r)) opened in
  S.destruct_star_l (points_to r n)
    (S.star (S.inv i (bit_cell r)) (S.mem_invariant (S.add_inv GS.empty i) opened)) opened;
  points_to_contents r n opened;
  introduce exists (v:bit). M.contents (physical m) r v with (FStar.Ghost.reveal n) and ()
