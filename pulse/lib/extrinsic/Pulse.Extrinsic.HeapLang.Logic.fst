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

let physical_full m = ()
let ghost_physical m m' = ()

let points_to_of #a r v =
  S.lift (H2.pts_to #(M.cell_value_of a) #(M.cell_pcm_of #a) r (M.Full v))

let points_to r v = points_to_of r v

let points_to_base_of (#a:Type0) (r:H.core_ref) (v:a) (m:S.full_mem)
  : Lemma (requires S.interp (points_to_of r v) m)
          (ensures H.interp (M.points_to_of r v) (physical m))
  = S.lift_eq (H2.pts_to #(M.cell_value_of a) #(M.cell_pcm_of #a) r (M.Full v))

let points_to_contents_of #a r v m =
  points_to_base_of r v m;
  M.points_to_contents_of r v (physical m)

let points_to_contents r v m = points_to_contents_of r v m

let points_to_intro_of #a r v m =
  S.lift_eq (H2.pts_to #(M.cell_value_of a) #(M.cell_pcm_of #a) r (M.Full v))

let points_to_intro r v m = points_to_intro_of r v m

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

let write_core (#a:Type0) (mask:S.inames) (r:H.core_ref) (old:FStar.Ghost.erased a) (desired:a)
  : IA.act unit mask (points_to_of r (FStar.Ghost.reveal old)) (fun _ -> points_to_of r desired)
  = IA.lift_mem_action #unit #false #mask
      (PM.upd_gen #(M.cell_value_of a) #(M.cell_pcm_of #a) r
        (M.Full (FStar.Ghost.reveal old)) (M.Full desired) (M.replace_of old desired))

let write_correspondence (#a:Type0) (mask:S.inames) (r:H.core_ref) (old:FStar.Ghost.erased a) (desired:a) (frame:S.slprop)
  (m:S.full_mem{Pulse.Extrinsic.Atomic.enabled mask (points_to_of r (FStar.Ghost.reveal old)) frame m})
  : Lemma (
      let _, next = write_core mask r old desired frame m in
      S.level next == S.level m /\ S.budget next == S.budget m /\
      M.store_of (physical m) r desired (physical next))
  =
  S.sep_laws ();
  S.destruct_star_l (points_to_of r (FStar.Ghost.reveal old)) (S.star frame (S.mem_invariant mask m)) m;
  points_to_base_of r (FStar.Ghost.reveal old) m;
  points_to_contents_of r (FStar.Ghost.reveal old) m;
  let update = M.replace_of old desired in
  let f = PM.upd_gen #(M.cell_value_of a) #(M.cell_pcm_of #a) r
    (M.Full (FStar.Ghost.reveal old)) (M.Full desired) update in
  let (| base_frame, restore |) = IA.pin_frame
    (PM.pts_to #(M.cell_value_of a) #(M.cell_pcm_of #a) r (M.Full (FStar.Ghost.reveal old)))
    (S.star frame (S.mem_invariant mask m)) m in
  let _, base_next = f base_frame (S.timeless_mem_of m) in
  let _, next = write_core mask r old desired frame m in
  S.destruct_star_l (points_to_of r desired) (S.star frame (S.mem_invariant mask next)) next;
  assert (next == S.update_timeless_mem m base_next);
  H.upd_gen_modifies r (M.Full (FStar.Ghost.reveal old)) (M.Full desired) update (physical m);
  let (| _, raw_next |) = H.upd_gen_action r (M.Full (FStar.Ghost.reveal old)) (M.Full desired) update (physical m) in
  assert (physical next == raw_next);
  points_to_contents_of r desired next

let write_memory_of #a mask r old desired frame m =
  write_correspondence mask r old desired frame m;
  let _, next = write_core mask r old desired frame m in
  next

let write_memory mask r old desired frame m = write_memory_of mask r old desired frame m
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

let points_to_exposed_of #a r v =
  exposed_lift (H2.pts_to #(M.cell_value_of a) #(M.cell_pcm_of #a) r (M.Full v));
  S.timeless_lift (H2.pts_to #(M.cell_value_of a) #(M.cell_pcm_of #a) r (M.Full v));
  R.entails_later (points_to_of r v)

let points_to_exposed r v = points_to_exposed_of r v

let allocation_fragment (#a:Type0) (v:a) (r:H.core_ref) (h:H.full_heap u#3)
  (h':M.heap{M.allocation_of h v r h'})
  : GTot (piece:M.heap {
      H.full_heap_pred h' /\ H.interp (M.points_to_of r v) piece /\
      H.disjoint piece h /\ H.join piece h == h' })
  = let addr = H.core_ref_as_addr r in
    H.select_some addr h';
    let piece = H.update_addr (H.empty_heap' (H.extent h')) addr
      (H.Ref (M.cell_value_of a) (M.cell_pcm_of #a) (M.Full v)) in
    FStar.PCM.compatible_refl (M.cell_pcm_of #a) (M.Full v);
    H.intro_pts_to #(M.cell_value_of a) #(M.cell_pcm_of #a) r (M.Full v) piece;
    introduce forall a. H.disjoint_addr piece h a
    with (if a = addr then () else ());
    assert (H.disjoint piece h);
    introduce forall a. H.select a (H.join piece h) == H.select a h'
    with (if a = addr then () else ());
    H.heap_ext (H.join piece h) h';
    introduce forall a. H.contains_addr h' a ==> H.full_cell (H.select_addr h' a)
    with (if a = addr then () else ());
    piece

let concrete_fragment (#a:Type0) (r:H.core_ref) (v:a) (piece:H.hheap (M.points_to_of r v))
  : GTot (extra:H2.heap u#3 {
      H2.concrete extra == piece /\ H2.ghost extra == H.empty_heap /\
      H2.interp (H2.pts_to #(M.cell_value_of a) #(M.cell_pcm_of #a) r (M.Full v)) extra })
  = { H2.concrete = piece; H2.ghost = H.empty_heap }

let allocate_memory_of #a mask v r heap frame m =
  S.sep_laws ();
  S.lift_emp_eq ();
  let base = S.timeless_mem_of m in
  let piece = allocation_fragment v r (physical m) heap in
  let extra = concrete_fragment r v piece in
  let next_base = { base with H2.concrete = heap } in
  let post = H2.pts_to #(M.cell_value_of a) #(M.cell_pcm_of #a) r (M.Full v) in
  let (| bf, restore |) = IA.pin_frame PM.emp (S.star frame (S.mem_invariant mask m)) m in
  assert_norm (PM.interp (PM.star PM.emp bf) base == H2.interp (H2.star H2.emp bf) base);
  H2.affine_star H2.emp bf base;
  H.join_empty (H2.ghost base);
  H2.intro_star post bf extra base;
  assert (H2.join extra base == next_base);
  restore post next_base;
  S.hogs_invariant_update_timeless_mem m next_base mask;
  S.inames_ok_update_timeless_mem m next_base mask;
  let next = S.update_timeless_mem m next_base in
  K.level_pack (S.level m) { (S.unpack m) with K.timeless_heap = next_base };
  K.credits_pack (S.level m) { (S.unpack m) with K.timeless_heap = next_base };
  next

let allocate_memory mask v r heap frame m = allocate_memory_of mask v r heap frame m
