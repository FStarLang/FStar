(*
   Copyright 2019 Microsoft Research

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
module Steel.Actions
open FStar.Real
open Steel.Memory
module U32 = FStar.UInt32
open FStar.FunctionalExtensionality

friend Steel.Memory

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

type hheap (fp:hprop) = h:heap{interp_heap fp h}

let depends_only_on_without_affinity (q:heap -> prop) (fp:hprop) =
  (forall (h0:hheap fp) (h1:heap{disjoint_heap h0 h1}). q h0 <==> q (join_heap h0 h1))

let frameable_heap_prop (fp:hprop) = q:(heap -> prop){q `depends_only_on_without_affinity` fp}

let hprop_of_lock_state (l:lock_state) : hprop =
  match l with
  | Available p -> p
  | Locked p -> p
  | Invariant p -> p

module L = FStar.List.Tot

val get_lock (l:lock_store) (i:nat{i < L.length l})
  : (prefix : lock_store &
     li : lock_state &
     suffix : lock_store {
       l == L.(prefix @ (li::suffix)) /\
       L.length (li::suffix) == i + 1
     })

#push-options "--fuel 1 --ifuel 1"
let rec get_lock l i =
  if i = L.length l - 1 then (
    (| [], L.hd l, L.tl l |)
  ) else
    let (| pre, li, suf |) = get_lock (L.tl l) i in
    (| (L.hd l) ::pre, li, suf |)
#pop-options

let lock_i (l:lock_store) (i:nat{i < L.length l}) : lock_state =
  let (| _, li, _ |) = get_lock l i in
  li


let lock_store_evolves : Preorder.preorder lock_store =
  fun (l1 l2 : lock_store) ->
    L.length l2 >= L.length l1 /\
    (forall (i:nat{i < L.length l1}).
       hprop_of_lock_state (lock_i l1 i) ==
       hprop_of_lock_state (lock_i l2 i)) /\
    (forall (i:nat{i < L.length l1}).
       Invariant? (lock_i l1 i) <==>
       Invariant? (lock_i l2 i))

let heap_evolves_seq
  (#t: Type)
  (#len: nat)
  (seq1: array_seq t len)
  (seq2: array_seq t len)
  (i:nat{i < len}) =
  select_pre seq1 i == select_pre seq2 i /\ (
    let x1 = Seq.index seq1 i in
    let x2 = Seq.index seq2 i in
    let pre = select_pre seq1 i in
    match x1.v_with_p, x2.v_with_p with
    | None, None -> pre None None
    | None, Some v2 -> pre None (Some v2.value)
    | Some v1, None -> pre (Some v1.value) None
    | Some v1, Some v2 -> pre (Some v1.value) (Some v2.value)
  )

let heap_evolves_addr (h1 h2 :heap) (addr: addr) =
  match h1 addr, h2 addr with
  | None, None
  | None, Some _ -> True
  | Some _, None -> False
  | Some (Array t1 len1 seq1 live1), Some (Array t2 len2 seq2 live2) ->
    ((not live1) ==> (not live2)) /\
    t1 == t2 /\ len1 == len2 /\
    (forall (i:nat{i < len1}). heap_evolves_seq seq1 seq2 i)

let heap_evolves' : Preorder.relation heap =
  fun (h1 h2: heap) ->
    forall (addr: addr). heap_evolves_addr h1 h2 addr

#push-options "--fuel 2 --ifuel 1"
let heap_evolves_reflexive () : Lemma (Preorder.reflexive heap_evolves') = ()
#pop-options

#push-options "--fuel 2 --ifuel 1 --warn_error -271"
let heap_evolves_transitive () : Lemma (Preorder.transitive heap_evolves') =
  let aux (h1 h2 h3: heap)
    : Lemma
      (requires (heap_evolves' h1 h2 /\ heap_evolves' h2 h3))
      (ensures (heap_evolves' h1 h3))
      [SMTPat ()]
  =
    let aux (addr: addr) : Lemma (heap_evolves_addr h1 h3 addr) =
      match h1 addr, h2 addr, h3 addr with
      | Some (Array t1 len1 seq1 live1), Some (Array t2 len2 seq2 live2),
        Some (Array t3 len3 seq3 live3) ->
        assert(t1 == t3);
        assert(len1 == len3);
        let aux (i:nat{i < len1}) : Lemma(heap_evolves_seq seq1 seq3 i) =
          assert(heap_evolves_seq seq1 seq2 i);
          assert(heap_evolves_seq seq2 seq3 i)
        in
        Classical.forall_intro aux
      | _ -> ()
    in
    Classical.forall_intro aux
  in
  ()
#pop-options

let heap_evolves : Preorder.preorder heap =
  heap_evolves_reflexive ();
  heap_evolves_transitive ();
  heap_evolves'

let mem_evolves : Preorder.preorder mem =
  fun m0 m1 -> lock_store_evolves m0.locks m1.locks /\ heap_evolves m0.heap m1.heap

let lock_store_unchanged_respects_preorder (m0 m1: mem) : Lemma
  (requires (m0.locks == m1.locks))
  (ensures (lock_store_evolves m0.locks m1.locks))
  =
  ()

let pre_action (fp:hprop) (a:Type) (fp':a -> hprop) =
  hheap fp -> (x:a & hheap (fp' x))

let is_frame_preserving (#a:Type) (#fp:hprop) (#fp':a -> hprop) (f:pre_action fp a fp') =
  forall (frame:hprop) (h0:heap).
    interp_heap (fp `star` frame) h0 ==>
    (let (| x, h1 |) = f h0 in
     interp_heap (fp' x `star` frame) h1 /\
     (forall (f_frame:frameable_heap_prop frame). f_frame h0 <==> f_frame h1) /\
     heap_evolves h0 h1
   )

let action (fp:hprop) (a:Type) (fp':a -> hprop) =
  f:pre_action fp a fp'{ is_frame_preserving f }


#push-options "--fuel 2 --ifuel 1"
let is_frame_preserving_intro
  (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_action fp a fp')
  (preserves_framing_intro:
    (frame: hprop) -> (h0: heap) ->
    Lemma (requires (interp_heap (fp `star` frame) h0)) (ensures (
      let (| x, h1 |) = f h0 in  interp_heap (fp' x `star` frame) h1
    ))
  )
  (preserves_frame_prop_intro:
    (frame: hprop) -> (h0: heap) ->
    (f_frame: frameable_heap_prop frame) ->
    Lemma (requires (interp_heap (fp `star` frame) h0)) (ensures (
      let (| x, h1 |) = f h0 in f_frame h0 <==> f_frame h1
    ))
  )
  (evolving:
    (h0: heap) -> (addr: addr) ->
    Lemma (requires (interp_heap fp h0)) (ensures (
      let (| x, h1 |) = f h0 in heap_evolves_addr h0 h1 addr
    ))
  )
  : Lemma (is_frame_preserving f)
  =
  let aux (frame: hprop) (h0: heap) : Lemma (interp_heap (fp `star` frame) h0 ==>
     (let (| x, h1 |) = f h0 in
     interp_heap (fp' x `star` frame) h1 /\
     (forall (f_frame:frameable_heap_prop frame). f_frame h0 <==> f_frame h1) /\
     heap_evolves h0 h1)
  ) =
    let aux (pf: (interp_heap (fp `star` frame) h0)) : Lemma (
      interp_heap (fp `star` frame) h0 /\ (
      let h0 : (h0:heap{interp_heap fp h0}) = affine_star_heap fp frame h0; h0 in
      let (| x, h1 |) = f h0 in
      interp_heap (fp' x `star` frame) h1 /\
      (forall (f_frame:frameable_heap_prop frame). f_frame h0 <==> f_frame h1) /\
      heap_evolves h0 h1)
    ) =
      affine_star_heap fp frame h0;
      let (| x, h1 |) = f h0 in
      let aux (f_frame:frameable_heap_prop frame)
        : Lemma (f_frame h0 <==> f_frame h1) =
        preserves_frame_prop_intro frame h0 f_frame
      in
      Classical.forall_intro aux;
      let aux (addr: addr) : Lemma (heap_evolves_addr h0 h1 addr) =
        evolving h0 addr
      in
      Classical.forall_intro aux;
      preserves_framing_intro frame h0
    in
    Classical.impl_intro aux
  in
  Classical.forall_intro_2 aux
#pop-options

let is_frame_preserving_elim
  (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_action fp a fp')
  (frame: hprop) (h0: heap)
  (f_frame:frameable_heap_prop frame)
  : Lemma (requires (is_frame_preserving f /\ interp_heap (fp `star` frame) h0)) (ensures (
     let (| x, h1 |) = f h0 in
     interp_heap (fp' x `star` frame) h1 /\
     f_frame h0 <==> f_frame h1 /\
     heap_evolves h0 h1
  ))
  = ()

let depends_only_on_without_affinity_elim
  (q:heap -> prop) (fp:hprop)
  (h0:hheap fp)
  (h1:heap{disjoint_heap h0 h1})
  : Lemma
    (requires (depends_only_on_without_affinity q fp))
    (ensures (q h0 <==> q (join_heap h0 h1)))
  = ()

#push-options "--z3rlimit 150 --fuel 1 --ifuel 0"
let pre_action_to_action
  (#fp:hprop) (#a: Type) (#fp': a -> hprop) (f: pre_action fp a fp')
  (action_preserves_frame_disjointness_addr:
    (frame: hprop) ->
    (h0:hheap fp) ->
    (h1:hheap frame{disjoint_heap h0 h1}) ->
    (addr: addr) ->
    Lemma (
      let (|_, h0'|) = f h0 in
      disjoint_addr h0' h1 addr
    )
  )
  (action_does_not_depend_on_framing_addr:
    (frame: hprop) ->
    (h0:hheap fp) ->
    (h1:hheap frame{disjoint_heap h0 h1}) ->
    (addr: addr) ->
    Lemma (requires (
      let (|_, h0'|) = f h0 in
      disjoint_heap h0' h1
    ))
    (ensures (
      let (|_, h0'|) = f h0 in
      let (|_, h'|) = f (join_heap h0 h1) in
      h' addr == join_heap h0' h1 addr
    ))
  )
  (action_result_does_not_depend_on_framing:
    (frame: hprop) ->
    (h0:hheap fp) ->
    (h1:hheap frame{disjoint_heap h0 h1}) ->
    Lemma (
      let (|x_alone, h0'|) = f h0 in
      let (|x_joint, h'|) = f (join_heap h0 h1) in
      x_alone == x_joint
    )
  )
  (evolving:
    (h0: heap) -> (addr: addr) ->
    Lemma (requires (interp_heap fp h0)) (ensures (
      let (| x, h1 |) = f h0 in heap_evolves_addr h0 h1 addr
    ))
  )
  : Tot (action fp a fp')
  =
  is_frame_preserving_intro f (fun frame h ->
    let (| x, h' |) = f h in
    let pf :squash (exists (h0:heap). (exists (h1:heap).
      disjoint_heap h0 h1 /\ h == join_heap h0 h1 /\ interp_heap fp h0 /\ interp_heap frame h1
    )) =
      assert(interp_heap (fp `star` frame) h)
    in
    Classical.exists_elim
      (interp_heap (fp' x `star` frame) h') pf
      (fun h0 ->
        let pf: squash (exists (h1: hheap frame).
          disjoint_heap h0 h1 /\ h == join_heap h0 h1 /\ interp_heap fp h0 /\ interp_heap frame h1
        ) =
          ()
        in
        Classical.exists_elim
          (interp_heap (fp' x `star` frame) h') pf
          (fun h1 ->
            let h0 : hheap fp = h0 in
            let h1 : (h1:hheap frame{disjoint_heap h0 h1 /\ h == join_heap h0 h1}) = h1 in
            let (|x_alone, h0'|) = f h0 in
            let (|x_joint, h'|) = f (join_heap h0 h1) in
            let aux (addr: addr) : Lemma (disjoint_addr h0' h1 addr) =
              action_preserves_frame_disjointness_addr frame h0 h1 addr
            in
            Classical.forall_intro aux;
            let aux (addr: addr) : Lemma (h' addr == join_heap h0' h1 addr) =
              action_does_not_depend_on_framing_addr frame h0 h1 addr
            in
            Classical.forall_intro aux;
            mem_equiv_eq h' (join_heap h0' h1);
            assert(interp_heap (fp' x_alone) h0');
            action_result_does_not_depend_on_framing frame h0 h1;
            assert(x_alone == x_joint);
            assert(interp_heap frame h1);
            assert(h' == join_heap h0' h1);
            assert(disjoint_heap h0' h1);
            intro_star_heap (fp' x) (frame) h0' h1;
            assert(interp_heap (fp' x `star` frame) h')
        )
    )
  ) (fun frame h f_frame ->
    let (| x, h' |) = f h in
    let pf :squash (exists (h0:heap). (exists (h1:heap).
      disjoint_heap h0 h1 /\ h == join_heap h0 h1 /\ interp_heap fp h0 /\ interp_heap frame h1
    )) =
      assert(interp_heap (fp `star` frame) h)
    in
    Classical.exists_elim
      (f_frame h <==> f_frame h') pf
      (fun h0 ->
        let pf: squash (exists (h1: hheap frame).
          disjoint_heap h0 h1 /\ h == join_heap h0 h1 /\ interp_heap fp h0 /\ interp_heap frame h1
        ) =
          ()
        in
        Classical.exists_elim
          (f_frame h <==> f_frame h') pf
          (fun h1 ->
           let h0 : hheap fp = h0 in
            let h1 : (h1:hheap frame{disjoint_heap h0 h1 /\ h == join_heap h0 h1}) = h1 in
            let (|x_alone, h0'|) = f h0 in
            let (|x_joint, h'|) = f (join_heap h0 h1) in
            let aux (addr: addr) : Lemma (disjoint_addr h0' h1 addr) =
              action_preserves_frame_disjointness_addr frame h0 h1 addr
            in
            Classical.forall_intro aux;
            let aux (addr: addr) : Lemma (h' addr == join_heap h0' h1 addr) =
              action_does_not_depend_on_framing_addr frame h0 h1 addr
            in
            Classical.forall_intro aux;
            mem_equiv_eq h' (join_heap h0' h1);
            assert(f_frame `depends_only_on_without_affinity` frame);
            depends_only_on_without_affinity_elim f_frame frame h1 h0;
            assert(f_frame h1 <==> f_frame (join_heap h1 h0));
            assert(join_heap h1 h0 == h);
            depends_only_on_without_affinity_elim f_frame frame h1 h0';
            assert(join_heap h1 h0' == h');
            assert(f_frame h <==> f_frame h')
          )
       )
  ) (fun h0 addr ->
    evolving h0 addr
  );
  f
#pop-options


let mem_invariant_elim' (uses:Set.set lock_addr) (hp:hprop) (m:mem)
: Lemma
  (requires interp_heap (hp `star` locks_invariant uses m) m.heap)
  (ensures
    interp_heap (hp `star` lock_store_invariant uses m.locks) m.heap /\
    (forall (i:nat). i >= m.ctr ==> m.heap i == None))
= refine_star_heap (lock_store_invariant uses m.locks) hp (heap_ctr_valid m);
  refine_equiv_heap (lock_store_invariant uses m.locks `star` hp) (heap_ctr_valid m) m.heap;
  star_commutative hp (lock_store_invariant uses m.locks)


let mem_invariant_elim (hp:hprop) (m:mem)
: Lemma
  (requires interp_heap (hp `star` locks_invariant Set.empty m) m.heap)
  (ensures
    interp_heap (hp `star` lock_store_invariant Set.empty m.locks) m.heap /\
    (forall (i:nat). i >= m.ctr ==> m.heap i == None))
  = mem_invariant_elim' Set.empty hp m

let mem_invariant_intro' (uses:Set.set lock_addr) (hp:hprop) (m:mem)
: Lemma
  (requires
    interp_heap (hp `star` lock_store_invariant uses m.locks) m.heap /\
    (forall (i:nat). i >= m.ctr ==> m.heap i == None))
  (ensures interp_heap (hp `star` locks_invariant uses m) m.heap)
= star_commutative hp (lock_store_invariant uses m.locks);
  refine_equiv_heap (lock_store_invariant uses m.locks `star` hp) (heap_ctr_valid m) m.heap;
  refine_star_heap (lock_store_invariant uses m.locks) hp (heap_ctr_valid m);
  star_commutative hp (locks_invariant uses m)

let mem_invariant_intro (hp:hprop) (m:mem)
: Lemma
  (requires
    interp_heap (hp `star` lock_store_invariant Set.empty m.locks) m.heap /\
    (forall (i:nat). i >= m.ctr ==> m.heap i == None))
  (ensures interp_heap (hp `star` locks_invariant Set.empty m) m.heap)
= mem_invariant_intro' Set.empty hp m

#push-options "--warn_error -271 --max_fuel 1 --initial_fuel 1"
let non_alloc_action_to_non_locking_pre_m_action
  (fp:hprop) (a: Type) (fp': a -> hprop) (f: action fp a fp')
  (non_alloc: (h: hheap fp) -> (addr: addr) -> Lemma
    (requires (h addr == None))
    (ensures (let (| _, h'|) = f h in h' addr == None))
  )
  : Tot (pre_m_action fp a fp')
  =
  fun m ->
    mem_invariant_elim fp m;
    let (|x, h'|) = f m.heap in
    let aux (i: addr) : Lemma (requires (i >= m.ctr)) (ensures (h' i == None)) [SMTPat ()]
      = non_alloc m.heap i
    in
    let does_not_perturb_locks (lock_p: hprop) (h:hheap (fp `star` lock_p))
      : Lemma (let (|_, h'|) = f h in interp_heap lock_p h') [SMTPat ()]
    =
      assert(is_frame_preserving f);
      assert(interp_heap (fp `star` lock_p) h);
      let (| x, h' |) = f h in
      assert(interp_heap (fp' x `star` lock_p) h');
      affine_star_heap (fp' x) lock_p h';
      assert(interp_heap lock_p h')
    in
    assert (interp_heap (lock_store_invariant Set.empty m.locks) h');
    let m':mem = {m with heap = h'} in
    mem_invariant_intro (fp' x) m';
    (| x, m' |)
#pop-options

let mprop_to_hprop0 (hp:hprop) (mp:mprop hp) : heap -> prop =
  fun h -> mp (mem_of_heap h)

#push-options "--warn_error -271"
let mprop_to_hprop_depends_only_on (hp:hprop) (mp:mprop hp)
: Lemma (mprop_to_hprop0 hp mp `depends_only_on_without_affinity` hp)
= let aux (h0:hheap hp) (h1:heap{disjoint_heap h0 h1})
    : Lemma ((mprop_to_hprop0 hp mp) h0 <==> (mprop_to_hprop0 hp mp) (join_heap h0 h1))
            [SMTPat ()]
    = assert (join (mem_of_heap h0) (mem_of_heap h1) ==
              mem_of_heap (join_heap h0 h1));
      assert (mp (mem_of_heap h0) <==> mp (join (mem_of_heap h0) (mem_of_heap h1)));
      assert (mp (mem_of_heap h0) <==> mp (mem_of_heap (join_heap h0 h1)))
  in
  ()

let mprop_to_hprop (hp:hprop) (mp:mprop hp) : (q:(heap -> prop){q `depends_only_on_without_affinity` hp}) =
  mprop_to_hprop_depends_only_on hp mp;
  mprop_to_hprop0 hp mp

open FStar.PropositionalExtensionality

let lift_fp_props_preservation_to_mprops (hp:hprop) (m0 m1:mem)
: Lemma
  (requires
    (forall (f_frame:(q:(heap -> prop){q `depends_only_on_without_affinity` hp})). f_frame (heap_of_mem m0) <==> f_frame (heap_of_mem m1)))
  (ensures
    (forall (mp:mprop hp). mp (core_mem m0) == mp (core_mem m1)))
= let aux (mp:mprop hp)
  : Lemma (mp (core_mem m0) == mp (core_mem m1))
          [SMTPat ()]
    = let q : (q:(heap -> prop){q `depends_only_on_without_affinity` hp}) = mprop_to_hprop hp mp in
      assert (q (heap_of_mem m0) <==> q (heap_of_mem m1));
      assert ((mprop_to_hprop hp mp) (heap_of_mem m0) <==> (mprop_to_hprop hp mp) (heap_of_mem m1));
      assert (mp (mem_of_heap (heap_of_mem m0)) <==> mp (mem_of_heap (heap_of_mem m1)));
      assert (mp (core_mem m0) <==> mp (core_mem m1));
      FStar.PropositionalExtensionality.apply (mp (core_mem m0)) (mp (core_mem m1))
  in
  ()
#pop-options


#push-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let is_m_frame_and_preorder_preserving_intro_aux
  (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_m_action fp a fp')
  (preserves_framing_intro:
    (frame: hprop) -> (m0: hmem_with_inv (fp `star` frame)) ->
    Lemma (ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
      let (| x, m1 |) = f m0 in
      interp ((fp' x `star` frame) `star` locks_invariant Set.empty m1) m1 /\
      mem_evolves m0 m1
    )
  )
  (frame_prop_preserves_intro:
    (frame: hprop) -> (m0: hmem_with_inv (fp `star` frame)) -> (f_frame: frameable_heap_prop frame) ->
    Lemma (ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
      let (| x, m1 |) = f m0 in
      f_frame (heap_of_mem m0) <==> f_frame (heap_of_mem m1)
    )
  )
  (frame: hprop) (m0: hmem_with_inv (fp `star` frame))
  : Lemma ((ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
      let (| x, m1 |) = f m0 in
      interp ((fp' x `star` frame) `star` locks_invariant Set.empty m1) m1 /\
      mem_evolves m0 m1 /\
      (forall (f_frame:frameable_heap_prop frame). f_frame (heap_of_mem m0) <==> f_frame (heap_of_mem m1)) /\
      (forall (mp:mprop frame). mp (core_mem m0) == mp (core_mem m1))))
  =
   ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
    let (| x, m1 |) = f m0 in
    preserves_framing_intro frame m0;
    let aux (f_frame: frameable_heap_prop frame) : Lemma (
      f_frame (heap_of_mem m0) <==> f_frame (heap_of_mem m1)
    ) =
      frame_prop_preserves_intro frame m0 f_frame
    in
    Classical.forall_intro aux;
    assert (forall (f_frame:frameable_heap_prop frame). f_frame (heap_of_mem m0) <==> f_frame (heap_of_mem m1));
    lift_fp_props_preservation_to_mprops frame m0 m1
#pop-options



#push-options "--max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let is_m_frame_and_preorder_preserving_intro
  (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_m_action fp a fp')
  (preserves_framing_intro:
    (frame: hprop) -> (m0: hmem_with_inv (fp `star` frame)) ->
    Lemma (ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
      let (| x, m1 |) = f m0 in
      interp ((fp' x `star` frame) `star` locks_invariant Set.empty m1) m1 /\
      mem_evolves m0 m1
    )
  )
  (frame_prop_preserves_intro:
    (frame: hprop) -> (m0: hmem_with_inv (fp `star` frame)) -> (f_frame: frameable_heap_prop frame) ->
    Lemma (ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
      let (| x, m1 |) = f m0 in
      f_frame (heap_of_mem m0) <==> f_frame (heap_of_mem m1)
    )
  )
  : Lemma (is_m_frame_and_preorder_preserving f)
  =
  Classical.forall_intro_2 (is_m_frame_and_preorder_preserving_intro_aux
    f
    preserves_framing_intro
    frame_prop_preserves_intro)
#pop-options

let trivial_fp_prop (hp:hprop) : frameable_heap_prop hp = fun _ -> True

#restart-solver

#push-options "--z3rlimit 10 --ifuel 1 --fuel 2"
let non_alloc_action_to_non_locking_m_action
  (#fp:hprop) (#a: Type) (#fp': a -> hprop) (f: action fp a fp')
  (non_alloc: (h: hheap fp) -> (addr: addr) -> Lemma
    (requires (h addr == None))
    (ensures (let (| _, h'|) = f h in h' addr == None))
  )
  : Tot (m_action fp a fp')
= let f_m = non_alloc_action_to_non_locking_pre_m_action fp a fp' f non_alloc in
  let preserves_framing_intro (frame:hprop) (m0:hmem_with_inv (fp `star` frame))
    : Lemma (ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
      let (| x, m1 |) = f_m m0 in
      interp_heap ((fp' x `star` frame) `star` locks_invariant Set.empty m1) m1.heap /\
      mem_evolves m0 m1
    )
    =
    let (| x, m1 |) = f_m m0 in
    assert (interp_heap ((fp `star` frame) `star` locks_invariant Set.empty m0) m0.heap);
    mem_invariant_elim (fp `star` frame) m0;
    assert (interp_heap ((fp `star` frame) `star` lock_store_invariant Set.empty m0.locks) m0.heap);
    star_associative fp frame (lock_store_invariant Set.empty m0.locks);
    assert (interp_heap (fp `star` (frame `star` lock_store_invariant Set.empty m0.locks)) m0.heap);
    is_frame_preserving_elim f (frame `star` (lock_store_invariant Set.empty m0.locks)) m0.heap
      (trivial_fp_prop (frame `star` (lock_store_invariant Set.empty m0.locks)));
    assert (interp_heap (fp' x `star` (frame `star` lock_store_invariant Set.empty m0.locks)) m1.heap);
    assert(lock_store_invariant Set.empty m0.locks == lock_store_invariant Set.empty m1.locks);
    assert (interp_heap (fp' x `star` (frame `star` lock_store_invariant Set.empty m1.locks)) m1.heap);
    star_associative (fp' x) frame (lock_store_invariant Set.empty m1.locks);
    assert (interp_heap ((fp' x `star` frame) `star` lock_store_invariant Set.empty m1.locks) m1.heap);
    mem_invariant_intro (fp' x `star` frame) m1;
    assert (interp_heap ((fp' x `star` frame) `star` locks_invariant Set.empty m1) (heap_of_mem m1));
    lock_store_unchanged_respects_preorder m0 m1;
    assert(heap_evolves m0.heap m1.heap);
    assert(mem_evolves m0 m1)
  in
  is_m_frame_and_preorder_preserving_intro f_m
    preserves_framing_intro
  (fun frame m0 f_frame ->
    ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
    let (| x, m1 |) = f_m m0 in
    is_frame_preserving_elim f frame m0.heap f_frame;
    assert(f_frame (heap_of_mem m0) <==> f_frame (heap_of_mem m1))
  );
  f_m
#pop-options

////////////////////////////////////////////////////////////////////////////////
// Locks
////////////////////////////////////////////////////////////////////////////////


let lock (p:hprop) = nat

let new_lock_pre_m_action (p:hprop)
  : pre_m_action p (lock p) (fun _ -> emp)
  = fun m ->
     mem_invariant_elim p m;
     let l = Available p in
     let locks' = l :: m.locks in
     assert (interp_heap (lock_store_invariant Set.empty locks') (heap_of_mem m));
     let mem :mem = { m with locks = locks' } in
     assert (lock_store_invariant Set.empty mem.locks == p `star` lock_store_invariant Set.empty m.locks);
     assert (interp_heap (lock_store_invariant Set.empty mem.locks) (heap_of_mem mem));
     emp_unit (lock_store_invariant Set.empty mem.locks);
     star_commutative emp (lock_store_invariant Set.empty mem.locks);
     assert (interp_heap (emp `star` lock_store_invariant Set.empty mem.locks) (heap_of_mem mem));
     let lock_id = List.Tot.length locks' - 1 in
     mem_invariant_intro emp mem;
     (| lock_id, mem |)

let equiv_star_left (p q r:hprop)
  : Lemma
    (requires q `equiv` r)
    (ensures (p `star` q) `equiv` (p `star` r))
  = Classical.forall_intro_2 equiv_heap_iff_equiv

let lock_store_evolves_intro (m:mem) (m1:mem{L.length m1.locks >= L.length m.locks})
  (same_lock_i: (i:nat{i < L.length m.locks}) ->
    Lemma (lock_i m.locks i == lock_i m1.locks i))
  : Lemma (requires L.length m1.locks >= L.length m.locks)
          (ensures lock_store_evolves m.locks m1.locks)
  = Classical.forall_intro same_lock_i

let emp_unit_left (p:hprop)
  : Lemma
    ((emp `star` p) `equiv` p)
  = emp_unit p;
    star_commutative emp p

#push-options "--warn_error -271 --fuel 1 --ifuel 0 --z3rlimit 10"
let new_lock_is_frame_preserving_aux (p:hprop) (frame:hprop) (m:hmem_with_inv (p `star` frame))
      : Lemma
          (ensures (
            ac_reasoning_for_m_frame_preserving p frame (locks_invariant Set.empty m) m;
            (
            let (| x, m1 |) = new_lock_pre_m_action p m in
            interp_heap (emp `star` frame `star` locks_invariant Set.empty m1) (heap_of_mem m1) /\
            mem_evolves m m1 /\
            (forall (mp:mprop frame). mp (core_mem m) == mp (core_mem m1))
            )))
      = ac_reasoning_for_m_frame_preserving p frame (locks_invariant Set.empty m) m;
        let (| x, m1 |) = new_lock_pre_m_action p m in

        mem_invariant_elim (p `star` frame) m;
        assert (m1.locks == Available p :: m.locks);
        assert (lock_store_invariant Set.empty m1.locks == (p `star` lock_store_invariant Set.empty m.locks));
        assert (interp_heap ((p `star` frame) `star` lock_store_invariant Set.empty m.locks) m.heap);
        star_associative p frame (lock_store_invariant Set.empty m.locks);
        assert (interp_heap (p `star` (frame `star` lock_store_invariant Set.empty m.locks)) m.heap);
        star_commutative frame (lock_store_invariant Set.empty m.locks);
        equiv_star_left p (frame `star` lock_store_invariant Set.empty m.locks) (lock_store_invariant Set.empty m.locks `star` frame);
        assert (interp_heap (p `star` (lock_store_invariant Set.empty m.locks `star` frame)) m.heap);
        star_associative p (lock_store_invariant Set.empty m.locks) frame;
        assert (interp_heap ((p `star` lock_store_invariant Set.empty m.locks) `star` frame) m.heap);
        assert (interp_heap ((lock_store_invariant Set.empty m1.locks) `star` frame) m.heap);
        assert (m.heap == m1.heap);
        star_commutative (lock_store_invariant Set.empty m1.locks) frame;
        assert (interp_heap (frame `star` (lock_store_invariant Set.empty m1.locks)) m1.heap);
        emp_unit_left (frame `star` (lock_store_invariant Set.empty m1.locks));
        assert (interp_heap (emp `star` (frame `star` (lock_store_invariant Set.empty m1.locks))) m1.heap);
        star_associative emp frame (lock_store_invariant Set.empty m1.locks);
        mem_invariant_intro (emp `star` frame) m1;

        let aux_lock_i (i:nat{i < L.length m.locks})
          : Lemma (lock_i m.locks i == lock_i m1.locks i)
          = let (| prefix, li, suffix |) = get_lock m.locks i in
            let (| prefix', li', suffix' |) = get_lock m1.locks i in
            L.append_cons_l (Available p) prefix (li::suffix);
            L.append_length_inv_tail (Available p:: prefix) (li::suffix) prefix' (li'::suffix')
        in
        lock_store_evolves_intro m m1 aux_lock_i

#push-options "--fuel 2 --ifuel 2"
let new_lock_is_frame_preserving (p:hprop)
  : Lemma (is_m_frame_and_preorder_preserving (new_lock_pre_m_action p))
  = Classical.forall_intro_2 (new_lock_is_frame_preserving_aux p)
#pop-options

let new_lock (p:hprop)
  : m_action p (lock p) (fun _ -> emp)
  = new_lock_is_frame_preserving p;
    new_lock_pre_m_action p

let lock_ok (#p:hprop) (l:lock p) (m:mem) =
  l < L.length m.locks /\
  (Available? (lock_i m.locks l) \/ Locked? (lock_i m.locks l)) /\
  hprop_of_lock_state (lock_i m.locks l) == p

let lock_ok_stable (#p:_) (l:lock p) (m0 m1:mem)
  : Lemma (lock_ok l m0 /\
           m0 `mem_evolves` m1 ==>
           lock_ok l m1)
  = ()

val lock_store_invariant_append (l1 l2:lock_store)
  : Lemma (lock_store_invariant Set.empty (l1 @ l2) `equiv`
           (lock_store_invariant Set.empty l1 `star` lock_store_invariant Set.empty l2))

#push-options "--fuel 1 --ifuel 1"
let rec lock_store_invariant_append l1 l2 =
  match l1 with
  | [] ->
    emp_unit (lock_store_invariant Set.empty l2);
    star_commutative emp (lock_store_invariant Set.empty l2)
  | hd::tl ->
    lock_store_invariant_append tl l2;
    assert (lock_store_invariant Set.empty (tl @ l2) `equiv`
      (lock_store_invariant Set.empty tl `star` lock_store_invariant Set.empty l2));
    match hd with
    | Available p | Invariant p ->
      calc (equiv) {
        lock_store_invariant Set.empty (l1 @ l2);
        (equiv) { }
        p `star` lock_store_invariant Set.empty (tl @ l2);
        (equiv) { star_congruence p (lock_store_invariant Set.empty (tl @ l2))
                    p (lock_store_invariant Set.empty tl `star` lock_store_invariant Set.empty l2) }
        p `star` (lock_store_invariant Set.empty tl `star` lock_store_invariant Set.empty l2);
        (equiv) {
          star_associative p (lock_store_invariant Set.empty tl) (lock_store_invariant Set.empty l2);
          star_congruence (p `star` lock_store_invariant Set.empty tl) (lock_store_invariant Set.empty l2)
            (lock_store_invariant Set.empty l1) (lock_store_invariant Set.empty l2) }
        lock_store_invariant Set.empty l1 `star` lock_store_invariant Set.empty l2;
      }
    | Locked _ -> ()

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let hmem_emp (p:hprop) (m:hmem_with_inv p) : hmem_with_inv emp = m
#pop-options

let middle_to_head (p q r:hprop) (h:hheap (p `star` (q `star` r)))
  : hheap (q `star` (p `star` r))
  = calc (equiv) {
      p `star` (q `star` r);
         (equiv) { star_associative p q r }
      (p `star` q) `star` r;
         (equiv) { star_commutative p q; equiv_extensional_on_star (p `star` q) (q `star` p) r }
      (q `star` p) `star` r;
         (equiv) { star_associative q p r }
      q `star` (p `star` r);
    };
    equiv_heap_iff_equiv (p `star` (q `star` r)) (q `star` (p `star` r));
    h

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 60"
let release #p l m
  = Classical.forall_intro_2 equiv_heap_iff_equiv;
    let (| prefix, li, suffix |) = get_lock m.locks l in
    let h = heap_of_mem m in
    lock_store_invariant_append prefix (li::suffix);
    mem_invariant_elim p m;
    assert (interp_heap (p `star`
                     (lock_store_invariant Set.empty prefix `star`
                       (lock_store_invariant Set.empty (li::suffix)))) h);
    match li with
    | Available _ ->
      (* this case is odd, but not inadmissible.
         We're releasing a lock that was not previously acquired.
         We could either fail, or just silently proceed.
         I choose to at least signal this case in the result
         so that we can decide to fail if we like, at a higher layer.

         Another cleaner way to handle this would be to insist
         that lockable resources are non-duplicable ...
         in which case this would be unreachable, since we have `p star p` *)
      (| false, hmem_emp p m |)

    | Locked _ ->
      assert (interp_heap (p `star`
                        (lock_store_invariant Set.empty prefix `star`
                          (lock_store_invariant Set.empty suffix))) h);
      let h = middle_to_head p (lock_store_invariant Set.empty prefix) (lock_store_invariant Set.empty suffix) h in
      assert (interp_heap (lock_store_invariant Set.empty prefix `star`
                        (p `star`
                          (lock_store_invariant Set.empty suffix))) h);
      let new_lock_store = prefix @ (Available p :: suffix) in
      lock_store_invariant_append prefix (Available p :: suffix);
      assert (lock_store_invariant Set.empty new_lock_store `equiv`
                (lock_store_invariant Set.empty prefix `star`
                 (p `star` lock_store_invariant Set.empty (suffix))));
      assert (interp_heap (lock_store_invariant Set.empty new_lock_store) h);
      emp_unit_left (lock_store_invariant Set.empty new_lock_store);
      let mem : mem = { m with locks = new_lock_store } in
      mem_invariant_intro emp mem;
      let mem : hmem_with_inv emp = mem in
      (| true, mem |)
#pop-options

///////////////////////////////////////////////////////////////////////////////
// Invariants
///////////////////////////////////////////////////////////////////////////////

let inv_ok (#p:hprop) (l:inv p) (m:mem) =
  l < L.length m.locks /\
  Invariant? (lock_i m.locks l) /\
  hprop_of_lock_state (lock_i m.locks l) == p

let inv_ok_stable (#p:_) (l:inv p) (m0 m1:mem)
  : Lemma (inv_ok l m0 /\
           m0 `mem_evolves` m1 ==>
           inv_ok l m1)
  = ()

let new_inv_pre_m_action (p:hprop)
  : pre_m_action p (inv p) (fun _ -> emp)
  = fun m ->
     let l = Invariant p in
     let locks' = l :: m.locks in
     mem_invariant_elim p m;
     assert (interp_heap (lock_store_invariant Set.empty locks') m.heap);
     let mem :mem = { m with locks = locks' } in
     assert (lock_store_invariant Set.empty mem.locks == p `star` lock_store_invariant Set.empty m.locks);
     assert (interp_heap (locks_invariant Set.empty mem) mem.heap);
     emp_unit (locks_invariant Set.empty mem);
     star_commutative emp (locks_invariant Set.empty mem);
     assert (interp_heap (emp `star` locks_invariant Set.empty mem) mem.heap);
     let lock_id = List.Tot.length locks' - 1 in
     (| lock_id, mem |)

#push-options "--warn_error -271 --fuel 1 --ifuel 0 --z3rlimit 10"
let new_inv_is_frame_preserving_aux (p:hprop) (frame:hprop) (m:hmem_with_inv (p `star` frame))
      : Lemma
          (ensures (
            ac_reasoning_for_m_frame_preserving p frame (locks_invariant Set.empty m) m;
            (
            let (| x, m1 |) = new_inv_pre_m_action p m in
            interp (emp `star` frame `star` locks_invariant Set.empty m1) m1 /\
            mem_evolves m m1 /\
            (forall (mp:mprop frame). mp (core_mem m) == mp (core_mem m1))
            )))
      = ac_reasoning_for_m_frame_preserving p frame (locks_invariant Set.empty m) m;
        let (| x, m1 |) = new_inv_pre_m_action p m in
        mem_invariant_elim (p `star` frame) m;
        assert (m1.locks == Invariant p :: m.locks);
        assert (lock_store_invariant Set.empty m1.locks == (p `star` lock_store_invariant Set.empty m.locks));
        assert (interp_heap ((p `star` frame) `star` lock_store_invariant Set.empty m.locks) m.heap);
        star_associative p frame (lock_store_invariant Set.empty m.locks);
        assert (interp_heap (p `star` (frame `star` lock_store_invariant Set.empty m.locks)) m.heap);
        star_commutative frame (lock_store_invariant Set.empty m.locks);
        equiv_star_left p (frame `star` lock_store_invariant Set.empty m.locks) (lock_store_invariant Set.empty m.locks `star` frame);
        assert (interp_heap (p `star` (lock_store_invariant Set.empty m.locks `star` frame)) m.heap);
        star_associative p (lock_store_invariant Set.empty m.locks) frame;
        assert (interp_heap ((p `star` lock_store_invariant Set.empty m.locks) `star` frame) m.heap);
        assert (interp_heap ((lock_store_invariant Set.empty m1.locks) `star` frame) m.heap);
        assert (heap_of_mem m == heap_of_mem m1);
        star_commutative (lock_store_invariant Set.empty m1.locks) frame;
        assert (interp_heap (frame `star` (lock_store_invariant Set.empty m1.locks)) m1.heap);
        emp_unit_left (frame `star` (lock_store_invariant Set.empty m1.locks));
        assert (interp_heap (emp `star` (frame `star` (lock_store_invariant Set.empty m1.locks))) m1.heap);
        star_associative emp frame (lock_store_invariant Set.empty m1.locks);
        mem_invariant_intro (emp `star` frame) m1;

        let aux_lock_i (i:nat{i < L.length m.locks})
          : Lemma (lock_i m.locks i == lock_i m1.locks i)
          = let (| prefix, li, suffix |) = get_lock m.locks i in
            let (| prefix', li', suffix' |) = get_lock m1.locks i in
            L.append_cons_l (Invariant p) prefix (li::suffix);
            L.append_length_inv_tail (Invariant p:: prefix) (li::suffix) prefix' (li'::suffix')
        in
        lock_store_evolves_intro m m1 aux_lock_i;
        lift_fp_props_preservation_to_mprops frame m m1
#pop-options

#push-options "--fuel 2 --ifuel 2"
let new_inv_is_frame_preserving (p:hprop)
  : Lemma (is_m_frame_and_preorder_preserving (new_inv_pre_m_action p))
  = Classical.forall_intro_2 (new_inv_is_frame_preserving_aux p)

let new_inv (p:hprop)
  : m_action p (inv p) (fun _ -> emp)
  = new_inv_is_frame_preserving p;
    new_inv_pre_m_action p

let promote_action_preatomic
    (#a:Type) (#fp:hprop) (#fp':a -> hprop)
    (uses:Set.set lock_addr)
    (f:action fp a fp')
    (non_alloc: (h: hheap fp) -> (addr: addr) -> Lemma
      (requires (h addr == None))
      (ensures (let (| _, h'|) = f h in h' addr == None))
    )
   : pre_atomic uses fp a fp' =
   fun (m0:hmem_with_inv' uses fp) ->
       mem_invariant_elim' uses fp m0;
       let h0 = heap_of_mem m0 in
       let (| x, h1 |) = f h0 in
       Classical.forall_intro (Classical.move_requires (non_alloc h0));
       let m1 = { m0 with heap = h1 } in
       mem_invariant_intro' uses (fp' x) m1;
       (| x, m1 |)

val action_to_atomic_frame_aux
    (uses:Set.set lock_addr)
    (#fp:hprop) (#a:Type) (#fp':a -> hprop)
    (f:action fp a fp')
    (non_alloc: (h: hheap fp) -> (addr: addr) -> Lemma
      (requires (h addr == None))
      (ensures (let (| _, h'|) = f h in h' addr == None))
    )
    (frame:hprop) (m0:hmem_with_inv' uses (fp `star` frame))
    : Lemma (
        ac_reasoning_for_m_frame_preserving fp frame (locks_invariant uses m0) m0;
        interp (fp `star` locks_invariant uses m0) m0 /\
        (let (| x, m1 |) = (promote_action_preatomic uses f non_alloc) m0 in
        interp ((fp' x `star` frame) `star` locks_invariant uses m1) m1 /\
        mem_evolves m0 m1 /\
        (forall (mp:mprop frame). mp (core_mem m0) == mp (core_mem m1))))

let action_to_atomic_frame_aux uses #fp #a #fp' f non_alloc frame m0 =
  ac_reasoning_for_m_frame_preserving fp frame (locks_invariant uses m0) m0;
  mem_invariant_elim' uses (fp `star` frame) m0;
  let h0 = heap_of_mem m0 in
  let (| x, h1 |) = f h0 in
  Classical.forall_intro (Classical.move_requires (non_alloc h0));
  let m1 = { m0 with heap = h1 } in

  let (| x', m1' |) = (promote_action_preatomic uses f non_alloc) m0 in
  assert (x == x');
  assert (m1 == m1');
  assert (m0.locks == m1.locks);
  assert (mem_evolves m0 m1);

  star_associative fp frame (lock_store_invariant uses m0.locks);
  star_associative (fp' x) frame (lock_store_invariant uses m1.locks);
  lift_fp_props_preservation_to_mprops frame m0 m1;
  mem_invariant_intro' uses (fp' x `star` frame) m1

val action_to_atomic_frame
    (uses:Set.set lock_addr)
    (#fp:hprop) (#a:Type) (#fp':a -> hprop)
    (f:action fp a fp')
    (non_alloc: (h: hheap fp) -> (addr: addr) -> Lemma
      (requires (h addr == None))
      (ensures (let (| _, h'|) = f h in h' addr == None))
    )
    :  Lemma (is_atomic_frame_and_preorder_preserving (promote_action_preatomic uses f non_alloc))

let action_to_atomic_frame uses #fp #a #fp' f non_alloc =
  Classical.forall_intro_2 (action_to_atomic_frame_aux uses f non_alloc)

let promote_action
    (#a:Type) (#fp:hprop) (#fp':a -> hprop)
    (uses:Set.set lock_addr)
    (is_ghost:bool)
    (f:action fp a fp')
    (non_alloc: (h: hheap fp) -> (addr: addr) -> Lemma
      (requires (h addr == None))
      (ensures (let (| _, h'|) = f h in h' addr == None))
    )
    : atomic uses is_ghost fp a fp' =
    action_to_atomic_frame uses f non_alloc;
    promote_action_preatomic uses f non_alloc

val atomic_satisfies_mem_evolves
  (#a:Type) (#fp:hprop) (#fp':a -> hprop) (#uses:Set.set lock_addr) (#is_ghost:bool)
  (f:atomic uses is_ghost fp a fp')
  (m0:hmem_with_inv' uses fp)
  : Lemma (let (| _, m1 |) = f m0 in mem_evolves m0 m1)

let atomic_satisfies_mem_evolves #a #fp #fp' #uses #is_ghost f m0 =
  calc (equiv) {
    fp `star` locks_invariant uses m0;
    (equiv) { emp_unit fp;
              star_congruence fp (locks_invariant uses m0) (fp `star` emp) (locks_invariant uses m0)}
    (fp `star` emp) `star` locks_invariant uses m0;
  };
  let m0:hmem_with_inv' uses (fp `star` emp) = m0 in
  let (| _, m1 |) = f m0 in
  ()

#push-options "--ifuel 1 --fuel 1"
let interp_inv_not_in_uses'
  (#p:hprop) (i:inv p)
  (uses:Set.set lock_addr)
  (m0:mem)
  : Lemma
  (requires inv_ok i m0 /\ not (i `Set.mem` uses))
  (ensures
    lock_store_invariant uses m0.locks `equiv`
    (p `star` lock_store_invariant (Set.union (Set.singleton i) uses) m0.locks))
  = let uses' = Set.union (Set.singleton i) uses in
    let rec aux_out_of_bounds (l:lock_store) (u:Set.set lock_addr) (i:nat{i >= L.length l})
      : Lemma (lock_store_invariant u l == lock_store_invariant (Set.union (Set.singleton i) u) l)
      = match l with
      | [] -> ()
      | hd::tl -> aux_out_of_bounds tl u i
    in
    let rec aux (l:lock_store) : Lemma
      (requires i < L.length l /\ Invariant? (lock_i l i) /\ hprop_of_lock_state (lock_i l i) == p)
      (ensures lock_store_invariant uses l `equiv` (p `star` lock_store_invariant uses' l))
      (decreases l)
      =
      let current_addr = L.length l - 1 in
      match l with
      | Invariant p' :: tl ->
        let (| prefix, li, suffix |) = get_lock l i in
        if i = current_addr then (
          L.append_length prefix (li::suffix);
          assert (p == p');
          assert (not (current_addr `Set.mem` uses));
          assert (lock_store_invariant uses l == p `star` lock_store_invariant uses tl);
          aux_out_of_bounds tl uses i
        ) else (
          let (| prefix', li', suffix' |) = get_lock tl i in
          L.append_length_inv_tail prefix (li::suffix) ((Invariant p')::prefix') (li'::suffix');
          assert (li == li');
          aux tl;
          if current_addr `Set.mem` uses then ()
          else (
            calc (equiv) {
              lock_store_invariant uses l;
              (equiv) { }
              p' `star` lock_store_invariant uses tl;
              (equiv) { star_congruence p' (lock_store_invariant uses tl) p' (p `star` lock_store_invariant uses' tl) }
              p' `star` (p `star` lock_store_invariant uses' tl);
              (equiv) { star_associative p' p (lock_store_invariant uses' tl);
                        star_commutative p p';
                        star_congruence (p' `star` p) (lock_store_invariant uses' tl)
                                        (p `star` p') (lock_store_invariant uses' tl);
                        star_associative p p' (lock_store_invariant uses' tl) }
              p `star` lock_store_invariant uses' l;
           }
          )
        )
      | hd::tl ->
        let (| prefix, li, suffix |) = get_lock l i in
        if i = current_addr then (
          L.append_length prefix (li::suffix);
          assert (prefix == [])
        ) else (
          let (| prefix', li', suffix' |) = get_lock tl i in
          L.append_length_inv_tail prefix (li::suffix) (hd::prefix') (li'::suffix');
          assert (li == li');
          aux tl;
          match hd with
          | Available p' ->
            calc (equiv) {
              lock_store_invariant uses l;
              (equiv) { }
              p' `star` lock_store_invariant uses tl;
              (equiv) { star_congruence p' (lock_store_invariant uses tl) p' (p `star` lock_store_invariant uses' tl) }
              p' `star` (p `star` lock_store_invariant uses' tl);
              (equiv) { star_associative p' p (lock_store_invariant uses' tl);
                        star_commutative p p';
                        star_congruence (p' `star` p) (lock_store_invariant uses' tl)
                                        (p `star` p') (lock_store_invariant uses' tl);
                        star_associative p p' (lock_store_invariant uses' tl) }
              p `star` lock_store_invariant uses' l;
           }
          | Locked _ -> ()
      )
    in aux m0.locks
#pop-options

let interp_inv_not_in_uses
  (#p:hprop) (i:inv p)
  (uses:Set.set lock_addr)
  (frame:hprop)
  (m0:mem)
  : Lemma
  (requires inv_ok i m0 /\ not (i `Set.mem` uses))
  (ensures
    (frame `star` lock_store_invariant uses m0.locks) `equiv`
    ((p `star` frame) `star` lock_store_invariant (Set.union (Set.singleton i) uses) m0.locks))
  = let istore' = lock_store_invariant (Set.union (Set.singleton i) uses) m0.locks in
    calc (equiv) {
         frame `star` lock_store_invariant uses m0.locks;
         (equiv) { interp_inv_not_in_uses' i uses m0;
                   star_congruence frame (lock_store_invariant uses m0.locks) frame
                     (p `star` istore') }
         frame `star` (p `star` istore');
         (equiv) { star_associative frame p istore';
                   star_commutative frame p;
                   star_congruence (frame `star` p) istore' (p `star` frame) istore'}
         (p `star` frame) `star` istore';
    }

val pre_with_invariant
  (#a:Type) (#fp:hprop) (#fp':a -> hprop) (#uses:Set.set lock_addr) (#is_ghost:bool)
  (#p:hprop)
  (i:inv p{not (i `Set.mem` uses)})
  (f:atomic (Set.union (Set.singleton i) uses) is_ghost (p `star` fp) a (fun x -> p `star` fp' x))
  : pre_atomic uses fp a fp'

let pre_with_invariant #a #fp #fp' #uses #is_ghost #p i f =
  fun (m0:hmem_with_inv' uses fp) ->
    assume (inv_ok i m0);
    mem_invariant_elim' uses fp m0;
    let uses' = Set.union (Set.singleton i) uses in
    interp_inv_not_in_uses i uses fp m0;
    mem_invariant_intro' uses' (p `star` fp) m0;
    let (| x, m1 |) = f m0 in
    mem_invariant_elim' uses' (p `star` fp' x) m1;
    atomic_satisfies_mem_evolves f m0;
    interp_inv_not_in_uses i uses (fp' x) m1;
    mem_invariant_intro' uses (fp' x) m1;
    (| x, m1 |)


val with_invariant_frame_aux
    (#fp:hprop) (#a:Type) (#fp':a -> hprop) (#uses:Set.set lock_addr) (#is_ghost:bool)
    (#p:hprop)
    (i:inv p{not (i `Set.mem` uses)})
    (f:atomic (Set.union (Set.singleton i) uses) is_ghost (p `star` fp) a (fun x -> p `star` fp' x))
    (frame:hprop) (m0:hmem_with_inv' uses (fp `star` frame))
    : Lemma (
        ac_reasoning_for_m_frame_preserving fp frame (locks_invariant uses m0) m0;
        interp (fp `star` locks_invariant uses m0) m0 /\
        (let (| x, m1 |) = (pre_with_invariant i f) m0 in
        interp ((fp' x `star` frame) `star` locks_invariant uses m1) m1 /\
        mem_evolves m0 m1 /\
        (forall (mp:mprop frame). mp (core_mem m0) == mp (core_mem m1))))

#push-options "--fuel 0 --ifuel 0"
let with_invariant_frame_aux #fp #a #fp' #uses #is_ghost #p i f frame m0 =
  mem_invariant_elim' uses (fp `star` frame) m0;
  assume (inv_ok i m0);
  ac_reasoning_for_m_frame_preserving fp frame (locks_invariant uses m0) m0;
  mem_invariant_elim' uses fp m0;
  let uses' = Set.union (Set.singleton i) uses in
  calc (equiv) {
    ((fp `star` frame) `star` lock_store_invariant uses m0.locks);
    (equiv) { interp_inv_not_in_uses i uses (fp `star` frame) m0 }
    (p `star` (fp `star` frame)) `star` lock_store_invariant uses' m0.locks;
    (equiv) { star_associative p fp frame;
              star_congruence ((p `star` fp) `star` frame) (lock_store_invariant uses' m0.locks)
                              (p `star` (fp `star` frame)) (lock_store_invariant uses' m0.locks)}
    ((p `star` fp) `star` frame) `star` lock_store_invariant uses' m0.locks;
  };
  calc (equiv) {
    fp `star` lock_store_invariant uses m0.locks;
    (equiv) { interp_inv_not_in_uses i uses fp m0 }
    (p `star` fp) `star` lock_store_invariant uses' m0.locks;
  };
  mem_invariant_intro' uses' ((p `star` fp) `star` frame) m0;
  mem_invariant_intro' uses' ((p `star` fp)) m0;
  let m0:hmem_with_inv' uses' ((p `star` fp) `star` frame) = m0 in
  let (| x, m1 |) = f m0 in
  mem_invariant_elim' uses' ((p `star` fp' x) `star` frame) m1;
  atomic_satisfies_mem_evolves f m0;
  calc (equiv) {
    ((p `star` fp' x) `star` frame) `star` lock_store_invariant uses' m1.locks;
    (equiv) { star_associative p (fp' x) frame;
              star_congruence ((p `star` fp' x) `star` frame) (lock_store_invariant uses' m1.locks)
                              (p `star` (fp' x `star` frame)) (lock_store_invariant uses' m1.locks)}
    (p `star` (fp' x `star` frame)) `star` lock_store_invariant uses' m1.locks;
    (equiv) { interp_inv_not_in_uses i uses (fp' x `star` frame) m1 }
    (fp' x `star` frame) `star` lock_store_invariant uses m1.locks;
  };
  mem_invariant_intro' uses (fp' x `star` frame) m1
#pop-options

val with_invariant_frame
    (#fp:hprop) (#a:Type) (#fp':a -> hprop) (#uses:Set.set lock_addr) (#is_ghost:bool)
    (#p:hprop)
    (i:inv p{not (i `Set.mem` uses)})
    (f:atomic (Set.union (Set.singleton i) uses) is_ghost (p `star` fp) a (fun x -> p `star` fp' x))
    :  Lemma (is_atomic_frame_and_preorder_preserving (pre_with_invariant i f))

let with_invariant_frame #fp #a #fp' #uses #is_ghost #p i f =
  Classical.forall_intro_2 (with_invariant_frame_aux i f)

let with_invariant #a #fp #fp' #uses #is_ghost #p i f =
    with_invariant_frame i f;
    pre_with_invariant i f

let promote_atomic_m_action #a #fp #fp' #is_ghost f = f


///////////////////////////////////////////////////////////////////////////////
// Utilities
///////////////////////////////////////////////////////////////////////////////

let rewrite_hprop_pre (p:hprop) (p':hprop{p `equiv` p'})
  : pre_action p unit (fun _ -> p')
  = equiv_heap_iff_equiv p p';
    fun h -> (| (), h |)

#push-options "--z3rlimit 15 --fuel 2 --ifuel 1"
let rewrite_hprop_action (p:hprop) (p':hprop{p `equiv` p'})
  : action p unit (fun _ -> p') =
  pre_action_to_action
    (rewrite_hprop_pre p p')
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 -> ())
    (fun h0 addr -> ())
#pop-options

let rewrite_hprop p p' =
  non_alloc_action_to_non_locking_m_action
    (rewrite_hprop_action p p')
    (fun h0 addr -> ())

let weaken_hprop_pre
  (p q:hprop)
  (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : pre_action p unit (fun _ -> q)
  = fun h -> proof (mem_of_heap h); (| (), h |)

#push-options "--z3rlimit 15 --fuel 2 --ifuel 1"
let weaken_hprop_action
  (p q:hprop)
  (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : action p unit (fun _ -> q) =
  pre_action_to_action
    (weaken_hprop_pre p q proof)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 -> ())
    (fun h0 addr -> ())
#pop-options

let weaken_hprop uses p q proof =
  promote_action
    uses
    true
    (weaken_hprop_action p q proof)
    (fun h0 addr -> ())

/////////////////////////////////////////////////////////////////////////////
// Arrays
/////////////////////////////////////////////////////////////////////////////

#push-options "--max_fuel 3"
let as_seq_heap (#t:_) (a:array_ref t) (m:hheap (array a)) : Seq.lseq t (U32.v (length a)) =
  match a with None -> Seq.empty | Some a ->
  let Array t' len' seq live = select_addr m a.array_addr in
  let len = U32.v a.array_length in
  assert(U32.v a.array_offset + U32.v a.array_length <= len');
  Seq.init len (fun i -> let x =  select_index seq (U32.v a.array_offset + i) in x.value)
#pop-options

let as_seq #t a m = as_seq_heap #t a m.heap


#push-options "--max_fuel 2"
let as_seq_lemma #t a i p m = ()
#pop-options

let read_array_addr
  (#t: _)
  (a:array_ref t{not (is_null_array a)})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i: U32.t{U32.v i < U32.v (length a)})
  (p: perm{readable p})
  (pre: Ghost.erased (Preorder.preorder (option t)))
  (m: hheap (pts_to_array_with_preorder a p iseq pre))
  : Tot (x:t{x == Seq.index iseq (U32.v i)})
  =
  let a = Some?.v a in
  match m a.array_addr with
  | Some (Array t' len seq live) ->
    assert(contains_index seq (U32.v a.array_offset + U32.v i));
    match (Seq.index seq (U32.v a.array_offset + U32.v i)).v_with_p with
    | None -> ()
    | Some x -> x.value
  | _ -> ()

let index_array_pre_action
  (#t: _)
  (a:array_ref t{not (is_null_array a)})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i: U32.t{U32.v i < U32.v (length a)})
  (p:perm{readable p})
  (pre: Ghost.erased (Preorder.preorder (option t)))
  : Tot (pre_action
    (pts_to_array_with_preorder a p iseq pre)
    (x:t{x == Seq.index iseq (U32.v i)})
    (fun _ -> pts_to_array_with_preorder a p iseq pre))
  = fun h ->
  let x = read_array_addr a iseq i p pre h in
  (| x, h |)

let index_array_action
  (#t: _)
  (a:array_ref t{not (is_null_array a)})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i: U32.t{U32.v i < U32.v (length a)})
  (p:perm{readable p})
  (pre: Ghost.erased (Preorder.preorder (option t)))
  : Tot (pre_action
    (pts_to_array_with_preorder a p iseq pre)
    (x:t{x == Seq.index iseq (U32.v i)})
    (fun _ -> pts_to_array_with_preorder a p iseq pre))
  =
  pre_action_to_action

    (index_array_pre_action a iseq i p pre)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 -> ())
    (fun h0 addr -> ())

let index_array
  (#t:_)
  (uses:Set.set lock_addr)
  (a:array_ref t{not (is_null_array a)})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: perm{readable p})
  (i:U32.t{U32.v i < U32.v (length a)}) =
  promote_action
    uses
    false
    (index_array_action a iseq i p (trivial_optional_preorder (trivial_preorder t)))
    (fun h addr -> ())

let update_array_addr
  (#t:_)
  (a: array_ref t{not (is_null_array a)})
  (iseq:  Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (perm:perm{readable perm})
  (pre: (Ghost.erased (Preorder.preorder (option t))){
    (Ghost.reveal pre) (Some (Seq.index iseq (U32.v i))) (Some v)
  })
  (m: hheap (pts_to_array_with_preorder a perm iseq pre))
  =
  let a = Some?.v a in
  match m a.array_addr with
  | Some (Array t' len seq live) ->
    on _ (fun a' ->
      if a.array_addr = a' then
        let new_seq = Seq.upd seq (U32.v i + U32.v a.array_offset) ({ preorder = pre;
          v_with_p = Some ({
            value = v; perm =  perm
          })
        }) in
        Some (Array t len new_seq live)
      else
        m a'
    )
   | _ -> m

#push-options "--max_fuel 2 --initial_fuel 2"
let upd_array_heap
  (#t:_)
  (a:array_ref t{not (is_null_array a)})
  (iseq:  Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (pre: (Ghost.erased (Preorder.preorder (option t))){
    (Ghost.reveal pre) (Some (Seq.index iseq (U32.v i))) (Some v)
  })
  (h: hheap (pts_to_array_with_preorder a full_perm iseq pre)) : heap =
  let a' = Some?.v a in
  let Array _ len v_orig _ = select_addr h a'.array_addr in
  update_array_addr a iseq i v full_perm pre h
#pop-options

#push-options "--z3rlimit 15 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let upd_array_heap_frame_disjointness_preservation
  (#t:_)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (pre: (Ghost.erased (Preorder.preorder (option t))){
    (Ghost.reveal pre) (Some (Seq.index iseq (U32.v i))) (Some v)
  })
  (h h0 h1:heap)
  (frame:hprop)
  : Lemma
    (requires
      disjoint_heap h0 h1 /\
      h == join_heap h0 h1 /\
      interp_heap (pts_to_array_with_preorder a full_perm iseq pre) h0 /\
      interp_heap frame h1)
    (ensures (
      let h0' = upd_array_heap a iseq i v pre h0 in
      disjoint_heap h0' h1))
  =
  ()
#pop-options

let upd_array_pre_action
  (#t:_)
  (a:array_ref t{not (is_null_array a)})
  (iseq:  Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (pre: (Ghost.erased (Preorder.preorder (option t))){
    (Ghost.reveal pre) (Some (Seq.index iseq (U32.v i))) (Some v)
  })
  : pre_action
    (pts_to_array_with_preorder a full_perm iseq pre)
    unit
    (fun _ -> pts_to_array_with_preorder a full_perm (Seq.upd iseq (U32.v i) v) pre)
  = fun h ->
    (| (), upd_array_heap a iseq i v pre h |)

#push-options "--z3rlimit 300 --fuel 2 --ifuel 1"
let upd_array_action_memory_split_independence
  (#t:_)
  (a:array_ref t{not (is_null_array a)})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (pre: (Ghost.erased (Preorder.preorder (option t))){
    (Ghost.reveal pre) (Some (Seq.index iseq (U32.v i))) (Some v)
  })
  (h h0 h1:heap)
  (frame:hprop)
  : Lemma
    (requires
      disjoint_heap h0 h1 /\
      h == join_heap h0 h1 /\
      interp_heap (pts_to_array_with_preorder a full_perm iseq pre) h0 /\
      interp_heap frame h1)
    (ensures (
      let (| _, h' |) = upd_array_pre_action a iseq i v pre h in
      let h0' = upd_array_heap a iseq i v pre h0 in
      upd_array_heap_frame_disjointness_preservation a iseq i v pre h h0 h1 frame;
      h' == (join_heap h0' h1)))
  =
  let (| _, h' |) = upd_array_pre_action a iseq i v pre h in
  let h0' = upd_array_heap a iseq i v pre h0 in
  upd_array_heap_frame_disjointness_preservation a iseq i v pre h h0 h1 frame;
  assert(disjoint_heap h0' h1);
  let aux (addr: addr) : Lemma (
    upd_array_heap_frame_disjointness_preservation a iseq i v pre h h0 h1 frame;
    assert(disjoint_heap h0' h1);
    h' addr == (join_heap h0' (h1 <: (m1:heap{disjoint_heap h0' m1}))) addr
  ) =
    let a = Some?.v a in
    if addr <> a.array_addr then () else
    if not (h1 `contains_addr` addr) then ()
    else match  h' addr, (join_heap h0' h1) addr with
    | Some (Array t2 len2 seq2 live2), Some (Array t3 len3 seq3 live3) ->
      assert(seq2 `Seq.equal` seq3)
    | _ -> ()
  in
  Classical.forall_intro aux;
  mem_equiv_eq h' (join_heap h0' h1)
#pop-options

let upd_array_action
  (#t:_)
  (a:array_ref t{not (is_null_array a)})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (pre: (Ghost.erased (Preorder.preorder (option t))){
    (Ghost.reveal pre) (Some (Seq.index iseq (U32.v i))) (Some v)
  })
  : Tot (
    action
      (pts_to_array_with_preorder a full_perm iseq pre)
      unit
      (fun _ -> pts_to_array_with_preorder a full_perm (Seq.upd iseq (U32.v i) v) pre)
    )
  =
  pre_action_to_action
    (upd_array_pre_action a iseq i v pre)
    (fun frame h0 h1 addr -> (* Disjointness preservation *)
      upd_array_heap_frame_disjointness_preservation a iseq i v pre (join_heap h0 h1) h0 h1 frame
    )
    (fun frame h0 h1 addr -> (* Does not depend on framing *)
      upd_array_action_memory_split_independence a iseq i v pre (join_heap h0 h1) h0 h1 frame
    )
    (fun frame h0 h1 -> (* Return  *)
      let (| x0, h |) = upd_array_pre_action a iseq i v pre h0 in
      let (| x1, h' |) = upd_array_pre_action a iseq i v pre (join_heap h0 h1) in
      assert (x0 == x1)
    )
    (fun h0 addr -> ())

let upd_array
  (#t:_)
  (uses:Set.set lock_addr)
  (a:array_ref t{not (is_null_array a)})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  : atomic
    uses
    false
    (pts_to_array a full_perm iseq)
    unit
    (fun _ -> pts_to_array a full_perm (Seq.upd iseq (U32.v i) v))
  =
  promote_action
    uses
    false
    (upd_array_action a iseq i v (trivial_optional_preorder (trivial_preorder t)))
    (fun h addr -> ())

let singleton_heap
  (#t: _)
  (len:U32.t)
  (init: t)
  (pre: Ghost.erased (Preorder.preorder (option t)))
  (a: array_ref t{
    U32.v len = U32.v (length a) /\
    U32.v len = U32.v (max_length a) /\
    0 = U32.v (offset a)
  })
  : hheap (pts_to_array_with_preorder a full_perm (Seq.Base.create (U32.v len) init) pre)
  =
  match a with None -> on _ (fun a' -> None) | Some a ->
  let h = on _ (fun a' ->
    if a' <> a.array_addr then None else
    Some (Array t (U32.v len) (Seq.init (U32.v len) (fun i ->
      { preorder = pre;
        v_with_p = Some ({
          value = init;
          perm = full_perm;
        })
      }
    )) true)
  ) in
  h

let intro_star_heap (p q:hprop) (mp:hheap p) (mq:hheap q)
  : Lemma
    (requires
      disjoint_heap mp mq)
    (ensures
      interp_heap (p `star` q) (join_heap mp mq))
  = ()

#push-options "--z3rlimit 20"
let star_commutative_heap (p1 p2:hprop)
  : Lemma (forall (h:heap). interp_heap (p1 `star` p2) h <==> interp_heap (p2 `star` p1) h)
  =
  ()
#pop-options


#push-options "--z3rlimit 10 --max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let alloc_array_pre_m_action
  (#t: _)
  (len:U32.t)
  (init: t)
  (pre: Ghost.erased (Preorder.preorder (option t)))
  : pre_m_action
    emp
    (a:array_ref t{length a = len /\ offset a = 0ul /\ max_length a = len})
    (fun a -> pts_to_array_with_preorder a full_perm (Seq.Base.create (U32.v len) init) pre)
  =  fun m ->
  mem_invariant_elim emp m;
  let a = if len = 0ul then None else Some ({
    array_addr = m.ctr;
    array_max_length = len;
    array_length = len;
    array_offset = 0ul;
  }) in
  let single_h = singleton_heap len init pre a in
  let new_h = join_heap (heap_of_mem m) single_h in
  assert(disjoint_heap m.heap single_h);
  affine_star emp (lock_store_invariant Set.empty m.locks) m;
  assert(interp_heap (lock_store_invariant Set.empty m.locks) m.heap);
  assert(interp_heap (
    pts_to_array_with_preorder a full_perm (Seq.Base.create (U32.v len) init) pre)
    single_h
  );
  intro_star_heap
    (lock_store_invariant Set.empty m.locks)
    (pts_to_array_with_preorder a full_perm (Seq.Base.create (U32.v len) init) pre)
    (heap_of_mem m)
    single_h;
  assert(interp_heap (
      (lock_store_invariant Set.empty m.locks) `star`
      (pts_to_array_with_preorder a full_perm (Seq.Base.create (U32.v len) init) pre)
    ) (join_heap (heap_of_mem m) single_h)
  );
  star_commutative_heap
    (lock_store_invariant Set.empty m.locks)
    (pts_to_array_with_preorder a full_perm (Seq.Base.create (U32.v len) init) pre);
  assert(interp_heap (
    (pts_to_array_with_preorder a full_perm (Seq.Base.create (U32.v len) init) pre)
    `star` (lock_store_invariant Set.empty m.locks)) new_h
  );
  let new_m = { m with heap = new_h; ctr = m.ctr +1 } in
  assert(forall i. i>= m.ctr + 1 ==> new_h i == None);
  mem_invariant_intro
    (pts_to_array_with_preorder a full_perm (Seq.Base.create (U32.v len) init) pre)
    new_m;
  (| a, new_m |)
#pop-options

#restart-solver

let ac_reasoning_for_m_frame_preserving'
  (p q r:hprop) (m:mem)
: Lemma
  (requires interp_heap ((p `star` q) `star` r) (heap_of_mem m))
  (ensures interp_heap (q `star` r) (heap_of_mem m))
= calc (equiv) {
    (p `star` q) `star` r;
       (equiv) { star_associative p q r }
    p `star` (q `star` r);
  };
  assert (interp_heap (p `star` (q `star` r)) (heap_of_mem m));
  affine_star_heap p (q `star` r) (heap_of_mem m)

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let alloc_array_is_m_frame_and_preorder_preserving
  (#t: _)
  (len:U32.t)
  (init: t)
  (pre: Preorder.preorder (option t))
  : Lemma (is_m_frame_and_preorder_preserving (
    alloc_array_pre_m_action len init pre)
  )
  =
  is_m_frame_and_preorder_preserving_intro (alloc_array_pre_m_action len init pre) (fun frame m ->
    mem_invariant_elim (emp `star` frame) m;
    let h = heap_of_mem m in
    let a : array_ref t = if len = 0ul then None else Some ({
      array_addr = m.ctr;
      array_max_length = len;
      array_length = len;
      array_offset = 0ul;
    }) in
    ac_reasoning_for_m_frame_preserving emp frame (locks_invariant Set.empty m) m;
    let (| a, m1 |) = alloc_array_pre_m_action len init pre m in
    assert (m1.ctr = m.ctr + 1);
    assert (m1.locks == m.locks);
    let h1 = heap_of_mem m1 in
    let single_h = singleton_heap len init pre a in
    assert (h1 == join_heap single_h h);
    intro_pts_to_array_with_preorder
      a full_perm (Seq.Base.create (U32.v len) init) pre single_h;
    assert (interp_heap (
      pts_to_array_with_preorder a full_perm (Seq.Base.create (U32.v len) init) pre) single_h
    );
    ac_reasoning_for_m_frame_preserving' emp frame (lock_store_invariant Set.empty m.locks) m;
    assert (interp_heap (frame `star` lock_store_invariant Set.empty m.locks) h);
    intro_star_heap
      (pts_to_array_with_preorder a full_perm (Seq.Base.create (U32.v len) init) pre)
      (frame `star` lock_store_invariant Set.empty m.locks)
      single_h
      h;
    assert (interp_heap
      (pts_to_array_with_preorder a full_perm (Seq.Base.create (U32.v len) init) pre
      `star` (frame `star` lock_store_invariant Set.empty m.locks)) h1
    );
    star_associative
      (pts_to_array_with_preorder a full_perm (Seq.Base.create (U32.v len) init) pre)
      frame
      (lock_store_invariant Set.empty m.locks);
    assert (interp_heap
      ((pts_to_array_with_preorder a full_perm (Seq.Base.create (U32.v len) init) pre
      `star` frame) `star` lock_store_invariant Set.empty m.locks) h1
    );
    mem_invariant_intro
      (pts_to_array_with_preorder a full_perm (Seq.Base.create (U32.v len) init) pre
      `star` frame)
      m1;
    assert(mem_evolves m m1)
  ) (fun frame m f_frame ->
   mem_invariant_elim (emp `star` frame) m;
   let h = heap_of_mem m in
    let a : array_ref t = if len = 0ul then None else Some ({
      array_addr = m.ctr;
      array_max_length = len;
      array_length = len;
      array_offset = 0ul;
    }) in
    ac_reasoning_for_m_frame_preserving emp frame (locks_invariant Set.empty m) m;
    let (| a, m1 |) = alloc_array_pre_m_action len init pre m in
    assert (m1.ctr = m.ctr + 1);
    assert (m1.locks == m.locks);
    let h1 = heap_of_mem m1 in
    let single_h = singleton_heap len init pre a in
    assert (h1 == join_heap single_h h);
    assert(depends_only_on_without_affinity f_frame frame);
    assert (interp_heap ((emp `star` frame) `star` (locks_invariant Set.empty m)) h);
    affine_star_heap (emp `star` frame) (locks_invariant Set.empty m) h;
    affine_star_heap emp frame h;
    assert(interp_heap frame h);
    assert(f_frame h <==> f_frame (join_heap single_h h))
  )
#pop-options

let alloc_array
  (#t: _)
  (len:U32.t)
  (init: t)
  : m_action
    emp
    (a:array_ref t{length a = len /\ offset a = 0ul /\ max_length a = len})
    (fun a -> pts_to_array a full_perm (Seq.Base.create (U32.v len) init))
  =
  alloc_array_is_m_frame_and_preorder_preserving len init
    (trivial_optional_preorder (trivial_preorder t));
  alloc_array_pre_m_action len init (trivial_optional_preorder (trivial_preorder t))

#push-options "--ifuel 1"
let free_array_pre_action
  (#t: _)
  (a: array_ref t{freeable a})
  : pre_action
    (array_perm a full_perm)
    unit
    (fun _ -> emp)
  = fun h -> (| (), on _ (fun a' ->
    let a_t = Some?.v a in
    if a_t.array_addr <> a' then h a' else match h a' with
    | Some (Array t' len seq live) ->
      assert(t' == t');
      let aux (i:nat{i < len}) : Lemma (
        Some? (Seq.index seq i).v_with_p /\
        (Some?.v (Seq.index seq i).v_with_p).perm == full_perm
      ) =
        assert(exists (contents: Ghost.erased (Seq.lseq t (U32.v (length a))))
          (pre: Preorder.preorder (option t)).
          interp_heap (pts_to_array_with_preorder a full_perm contents pre) h
        );
        let pf: squash (exists (contents: Ghost.erased (Seq.lseq t (U32.v (length a)))). (
          exists (pre: Preorder.preorder (option t)).
            interp_heap (pts_to_array_with_preorder a full_perm contents pre) h
          )
        ) = () in
        Classical.exists_elim
          (Some? (Seq.index seq i).v_with_p /\
            (Some?.v (Seq.index seq i).v_with_p).perm == full_perm)
          pf (fun contents ->
            let pf : squash (exists (pre: Preorder.preorder (option t)).
            interp_heap (pts_to_array_with_preorder a full_perm contents pre) h
            ) = () in
            Classical.exists_elim
              (Some? (Seq.index seq i).v_with_p /\
                (Some?.v (Seq.index seq i).v_with_p).perm == full_perm)
              pf (fun pre ->
                assert(interp_heap (pts_to_array_with_preorder a full_perm contents pre) h);
                assert(contains_index seq i);
                let x = select_index seq i in
                assert(full_perm `lesser_equal_perm` x.perm)
              )
        )
      in
      Classical.forall_intro aux;
      assert(all_full_permission seq);
      Some (Array t len seq false)
    | _ -> h a'
  )|)
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let free_array_action
  (#t: _)
  (a: array_ref t{freeable a})
  =
  pre_action_to_action
    (free_array_pre_action a)
    (fun frame h0 h1 addr ->
      let a' = Some?.v a in
      let (| _, h0' |) = free_array_pre_action a h0 in
      if addr <> a'.array_addr then () else
      match h0' addr, h1 addr with
      | Some (Array t0 len0 seq0 live0), Some (Array t1 len1 seq1 live1) ->
        assert(not live0)
      | _ -> ()
    )
    (fun frame h0 h1 addr ->
      let (| _, h0' |) = free_array_pre_action a h0 in
      let (|_, h'|) = free_array_pre_action a (join_heap h0 h1) in
      match h' addr, h0' addr, h1 addr, (join_heap h0' h1) addr with
      | Some (Array t' len' seq' live'), Some (Array t0' len0' seq0' live0'),
        Some (Array t1 len1 seq1 live1), Some (Array tj lenj seqj livej) ->
        assert(exists (contents: Ghost.erased (Seq.lseq t (U32.v (length a))))
          (pre: Preorder.preorder (option t)).
          interp_heap (pts_to_array_with_preorder a full_perm contents pre) h0
        );
        let pf: squash (exists (contents: Ghost.erased (Seq.lseq t (U32.v (length a)))). (
          exists (pre: Preorder.preorder (option t)).
            interp_heap (pts_to_array_with_preorder a full_perm contents pre) h0
          )
        ) = () in
        Classical.exists_elim
          (h' addr == (join_heap h0' h1) addr)
          pf (fun contents ->
            let pf : squash (exists (pre: Preorder.preorder (option t)).
            interp_heap (pts_to_array_with_preorder a full_perm contents pre) h0
            ) = () in
            Classical.exists_elim
              (h' addr == (join_heap h0' h1) addr)
              pf (fun pre ->
                assert(seq' `Seq.equal` seqj)
              )
          )
      | _ -> ()
    )
    (fun frame h0 h1  -> ())
    (fun h0 addr -> ())
#pop-options

let free_array
  (#t: _)
  (a: array_ref t{freeable a})
  : m_action
    (array_perm a full_perm)
    unit
    (fun _ -> emp)
  =
  non_alloc_action_to_non_locking_m_action
    (free_array_action a)
    (fun h addr -> ())

#push-options "--fuel 2 --ifuel 1 --z3rlimit 300"
let share_array_pre_action
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (perm: perm{readable perm})
  (pre: Ghost.erased (Preorder.preorder (option t)))
  : pre_action
    (pts_to_array_with_preorder a perm iseq pre)
    (a':array_ref t{
      length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
       (not (is_null_array a) ==> address a = address a')
    })
    (fun a' -> star
      (pts_to_array_with_preorder a (half_perm perm) iseq pre)
      (pts_to_array_with_preorder a' (half_perm perm) (Ghost.hide (Ghost.reveal iseq)) pre)
    )
    = fun h -> match a with
    | None ->
      let a' = a in
      intro_star_heap
        (pts_to_array_with_preorder a (half_perm perm) iseq pre)
        (pts_to_array_with_preorder a'
          (half_perm perm)
          (Ghost.hide (Ghost.reveal iseq)) pre)
        h
        (on _ (fun a' -> None));
      mem_equiv_eq h (join_heap h (on _ (fun a' -> None)));
      (| a, h |)
    | Some a ->
      let split_h_1 : heap = on _ (fun addr ->
        if addr <> a.array_addr then h addr else
        match h a.array_addr with
        | Some (Array t len seq live) ->
          let new_seq = Seq.init len (fun i ->
            if i < U32.v a.array_offset || i >= U32.v a.array_offset + U32.v a.array_length then
              Seq.index seq i
            else match (Seq.index seq i).v_with_p with
            | None -> { preorder = select_pre seq i; v_with_p = None }
            | Some x ->
              assert(perm `lesser_equal_perm` x.perm);
              let new_p = sub_permissions x.perm (half_perm perm) in
              { preorder = select_pre seq i;
                v_with_p = Some ({x with perm = new_p})
              }
          ) in
          assert(Seq.length new_seq = len);
          Some (Array t len new_seq live)
        | _ -> h addr
      ) in
      let split_h_2 : heap = on _ (fun addr ->
        if addr <> a.array_addr then None else
        match h a.array_addr with
        | Some (Array t len seq live) ->
          let new_seq = Seq.init len (fun i ->
            if i < U32.v a.array_offset || i >= U32.v a.array_offset + U32.v a.array_length then
              { preorder = select_pre seq i; v_with_p = None }
            else match (Seq.index seq i).v_with_p with
            | None -> { preorder = select_pre seq i; v_with_p = None }
            | Some x ->
              { preorder = select_pre seq i; v_with_p =
                Some ({x with perm = half_perm perm})
              }
          ) in
          assert(Seq.length new_seq = len);
          Some (Array t len new_seq live)
        | _ -> None
      ) in
      let aux (addr: addr) : Lemma (disjoint_addr split_h_1 split_h_2 addr) =
         if addr <> a.array_addr then () else match split_h_1 addr, split_h_2 addr with
         | Some (Array t1 len1 seq1 live1), Some (Array t2 len2 seq2 live2) ->
           let aux (i:nat{i < len1}) : Lemma (
             select_pre seq1 i == select_pre seq2 i /\ (
             match contains_index seq1 i, contains_index seq2 i with
              | true, true ->
                let x1 = select_index seq1 i in
	        let x2 = select_index seq2 i in
                x1.value == x2.value /\ summable_permissions x1.perm x2.perm
             | _ -> True
           )) =
             ()
           in
           Classical.forall_intro aux
      in
      Classical.forall_intro aux;
      assert(disjoint_heap split_h_1 split_h_2);
      let aux (addr: addr) : Lemma (h addr == (join_heap split_h_1 split_h_2) addr) =
        if addr <> a.array_addr then () else
        match h addr, (join_heap split_h_1 split_h_2) addr with
        | Some (Array _ _ seq _), Some (Array _ _ joint_seq _) ->
           assert(seq `Seq.equal` joint_seq)
        | _ -> ()
      in
      Classical.forall_intro aux;
      mem_equiv_eq h (join_heap split_h_1 split_h_2);
      assert(h == join_heap split_h_1 split_h_2);
      (| Some a, h |)
#pop-options

let share_array_action
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (perm: perm{readable perm})
  (pre: Ghost.erased (Preorder.preorder (option t)))
  : action
    (pts_to_array_with_preorder a perm iseq pre)
    (a':array_ref t{
      length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
      (not (is_null_array a) ==> address a = address a')
    })
    (fun a' -> star
      (pts_to_array_with_preorder a (half_perm perm) iseq pre)
      (pts_to_array_with_preorder a' (half_perm perm) (Ghost.hide (Ghost.reveal iseq)) pre)
    )
  =
  pre_action_to_action
    (share_array_pre_action a iseq perm pre)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 ->
      let (|x_alone, h0'|) = share_array_pre_action a iseq perm pre h0 in
      let (|x_joint, h'|) = share_array_pre_action a iseq perm pre (join_heap h0 h1) in
      assert(x_alone == x_joint)
    )
    (fun h0 addr -> ())

let share_array_with_preorder
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (perm: perm{readable perm})
  (pre: Ghost.erased (Preorder.preorder (option t)))
  : m_action
    (pts_to_array_with_preorder a perm iseq pre)
    (a':array_ref t{
      length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
      (not (is_null_array a) ==> address a = address a')
    })
    (fun a' -> star
      (pts_to_array_with_preorder a (half_perm perm) iseq pre)
      (pts_to_array_with_preorder a' (half_perm perm) (Ghost.hide (Ghost.reveal iseq)) pre)
    )
    =
    non_alloc_action_to_non_locking_m_action
      (share_array_action a iseq perm pre)
      (fun h addr -> ())


let share_array
  (#t: _)
  (uses:Set.set lock_addr)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (perm: perm{readable perm})
  : atomic
    uses
    false
    (pts_to_array a perm iseq)
    (a':array_ref t{
      length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
      (not (is_null_array a) ==> address a = address a')
    })
    (fun a' -> star
      (pts_to_array a (half_perm perm) iseq)
      (pts_to_array a' (half_perm perm) (Ghost.hide (Ghost.reveal iseq)))
    )
    =
    promote_action
      uses
      false
      (share_array_action a iseq perm (trivial_optional_preorder (trivial_preorder t)))
      (fun h addr -> ())

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let starred_permissions_summable
  (#t: _)
  (a: array_ref t{not (is_null_array a)})
  (a':array_ref t{
    length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
    address a = address a'
  })
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: perm{readable p})
  (p': perm{readable p'})
  (pre: Ghost.erased (Preorder.preorder (option t)))
  (h: hheap (star
      (pts_to_array_with_preorder a p iseq pre)
      (pts_to_array_with_preorder a' p' (Ghost.hide (Ghost.reveal iseq)) pre)
    )
  )
  : Lemma (summable_permissions p p')
  =
  let pf : squash (exists (h0: heap). exists (h1: heap{disjoint_heap h0 h1}).
    interp_heap (pts_to_array_with_preorder a p iseq pre) h0 /\
    interp_heap (pts_to_array_with_preorder a' p' (Ghost.hide (Ghost.reveal iseq)) pre) h1 /\
    h == join_heap h0 h1
  ) =
    ()
  in
  Classical.exists_elim (summable_permissions p p') pf (fun h0 ->
    let pf : squash (exists (h1: heap{disjoint_heap h0 h1}).
      interp_heap (pts_to_array_with_preorder a p iseq pre) h0 /\
      interp_heap (pts_to_array_with_preorder a' p' (Ghost.hide (Ghost.reveal iseq)) pre) h1 /\
      h == join_heap h0 h1
    ) =
      ()
    in
    Classical.exists_elim (summable_permissions p p') pf (fun h1 ->
      match a, a' with
      | Some _, Some _ -> begin
        match h0 (address a), h1 (address a') with
        | Some (Array t0 len0 seq0 live0), Some (Array t1 len1 seq1 live1) ->
          assert(disjoint_addr h0 h1 (address a));
          assert(contains_index seq0 (U32.v (offset a)));
          assert(contains_index seq1 (U32.v (offset a')));
          let x0 = select_index seq0 (U32.v (offset a)) in
	  let x1 = select_index seq1 (U32.v (offset a')) in
          assert(summable_permissions x0.perm x1.perm)
        | _ -> ()
      end
      | _ -> ()
    )
  )
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let gather_array_pre_action
  (#t: _)
  (a: array_ref t)
  (a':array_ref t{
    length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
    (not (is_null_array a) ==> address a = address a')
  })
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: perm{readable p})
  (p': perm{readable p'})
  (pre: Ghost.erased (Preorder.preorder (option t)))
  : pre_action
    (star
      (pts_to_array_with_preorder a p iseq pre)
      (pts_to_array_with_preorder a' p' (Ghost.hide (Ghost.reveal iseq)) pre)
    )
    unit
    (fun _ -> pts_to_array_with_preorder a (sum_perm p p') iseq pre)
  = fun h ->
    match a with
    | None ->
      intro_pts_to_array_with_preorder a (sum_perm p p') iseq pre h;
      (| (), h |)
    | Some _ ->
      starred_permissions_summable a a' iseq p p' pre h;
      (| (), h |)
#pop-options

#push-options "--ifuel 1 --z3rlimit 30"
let gather_array_action
  (#t: _)
  (a: array_ref t)
  (a':array_ref t{
    length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
    (not (is_null_array a) ==> address a = address a')
  })
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: perm{readable p})
  (p': perm{readable p'})
  (pre: Ghost.erased (Preorder.preorder (option t)))
  : action
    (star
      (pts_to_array_with_preorder a p iseq pre)
      (pts_to_array_with_preorder a' p' (Ghost.hide (Ghost.reveal iseq)) pre)
    )
    unit
    (fun _ -> pts_to_array_with_preorder a (sum_perm p p') iseq pre)
  =
  pre_action_to_action
    (gather_array_pre_action a a' iseq p p' pre)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 -> ())
    (fun h0 addr -> ())
#pop-options

let gather_array
  (#t: _)
  (uses:Set.set lock_addr)
  (a: array_ref t)
  (a':array_ref t{
    length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
    (not (is_null_array a) ==> address a = address a')
  })
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: perm{readable p})
  (p': perm{readable p'})
  : atomic
    uses
    false
    (star
      (pts_to_array a p iseq)
      (pts_to_array a' p' (Ghost.hide (Ghost.reveal iseq)))
    )
    unit
    (fun _ -> pts_to_array a (sum_perm p p') iseq)
    =
    promote_action
      uses
      false
      (gather_array_action a a' iseq p p' (trivial_optional_preorder (trivial_preorder t)))
      (fun h addr -> ())

#restart-solver

let split_array_heaps
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: perm{readable p})
  (i:U32.t{U32.v i <= U32.v (length a)})
  (pre: Ghost.erased (Preorder.preorder (option t)))
  (h: hheap (pts_to_array_with_preorder a p iseq pre))
  : Pure (heap & heap) (requires (Some? a)) (ensures (fun _ -> True))
  =
   let a' = Some?.v a in
   let split_h_1 : heap = on _ (fun addr ->
      if addr <> a'.array_addr then h addr else
      match h a'.array_addr with
      | Some (Array t len seq live) ->
        let new_seq = Seq.init len (fun j ->
          if j < U32.v a'.array_offset || j >= U32.v a'.array_offset + U32.v a'.array_length then
            Seq.index seq j
          else if j <  U32.v a'.array_offset + U32.v i then
            Seq.index seq j
          else  { preorder = select_pre seq j; v_with_p = None }
        ) in
        assert(Seq.length new_seq = len);
        Some (Array t len new_seq live)
      | _ -> h addr
    ) in
    let split_h_2 : heap = on _ (fun addr ->
      if addr <> a'.array_addr then None else
      match h a'.array_addr with
      | Some (Array t len seq live) ->
        let new_seq = Seq.init len (fun j ->
          if j < U32.v a'.array_offset || j >= U32.v a'.array_offset + U32.v a'.array_length then
            { preorder = select_pre seq j; v_with_p = None }
          else if j <  U32.v a'.array_offset + U32.v i then
            { preorder = select_pre seq j; v_with_p = None }
          else Seq.index seq j
        ) in
        assert(Seq.length new_seq = len);
        Some (Array t len new_seq live)
      | _ -> h addr
    ) in
    (split_h_1, split_h_2)


#push-options "--fuel 2 --ifuel 1"
let split_array_heaps_disjoint
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: perm{readable p})
  (i:U32.t{U32.v i <= U32.v (length a)})
  (pre: Ghost.erased (Preorder.preorder (option t)))
  (h: hheap (pts_to_array_with_preorder a p iseq pre))
  : Lemma (requires (Some? a)) (ensures (
    let split_h_1, split_h_2 = split_array_heaps a iseq p i pre h in
    disjoint_heap split_h_1 split_h_2
  ))
  =
  ()
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let split_array_heaps_joint_equal
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: perm{readable p})
  (i:U32.t{U32.v i <= U32.v (length a)})
  (pre: Ghost.erased (Preorder.preorder (option t)))
  (h: hheap (pts_to_array_with_preorder a p iseq pre))
  : Lemma (requires (Some? a)) (ensures (
    let split_h_1, split_h_2 = split_array_heaps a iseq p i pre h in
    split_array_heaps_disjoint a iseq p i pre h;
    h == join_heap split_h_1 split_h_2
  ))
  =
  let a' = Some?.v a in
  let split_h_1, split_h_2 = split_array_heaps a iseq p i pre h in
  split_array_heaps_disjoint a iseq p i pre h;
  let aux (addr: addr) : Lemma (h addr == (join_heap split_h_1 split_h_2) addr) =
      if addr <> a'.array_addr then () else
      match h addr, (join_heap split_h_1 split_h_2) addr, split_h_1 addr, split_h_2 addr with
      | Some (Array _ _ seq _), Some (Array _ _ joint_seq _),
        Some (Array _ _ seq1 _), Some (Array _ _ seq2 _) ->
        assert(seq `Seq.equal` joint_seq)
      | _ -> ()
    in
  Classical.forall_intro aux;
  mem_equiv_eq h (join_heap split_h_1 split_h_2)
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let split_array_pre_action
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: perm{readable p})
  (i:U32.t{U32.v i <= U32.v (length a)})
  (pre: Ghost.erased (Preorder.preorder (option t)))
  : pre_action
    (pts_to_array_with_preorder a p iseq pre)
    (as:(array_ref t & array_ref t){(
      length (fst as) = i /\ length (snd as) = U32.sub (length a) i /\
      (not (is_null_array a) ==>
        (U32.v i > 0 ==> address (fst as) = address a /\ max_length (fst as) = max_length a /\
          offset (fst as) = offset a) /\
        (U32.v i < U32.v (length a) ==> address (snd as) = address a /\
          max_length (snd as) = max_length a /\ offset (snd as) = U32.add (offset a) i)
      )
    )})
    (fun (a1, a2) -> star
      (pts_to_array_with_preorder a1 p (Seq.slice iseq 0 (U32.v i)) pre)
      (pts_to_array_with_preorder a2 p (Seq.slice iseq (U32.v i) (U32.v (length a))) pre)
    )
  = fun h -> match a with
  | None ->
    intro_star_heap
      (pts_to_array_with_preorder a p (Seq.slice iseq 0 (U32.v i)) pre)
      (pts_to_array_with_preorder a p (Seq.slice iseq (U32.v i) (U32.v (length a))) pre)
      h
      (on _ (fun a' -> None));
    mem_equiv_eq h (join_heap h (on _ (fun a' -> None)));
    (| (a, a), h |)
  | Some a' ->
      let a1: array_ref t = if i = 0ul then None else Some ({ a' with
        array_offset = a'.array_offset;
        array_length = i;
      }) in
      let a2: array_ref t = if i = a'.array_length then None else Some ({ a' with
        array_offset = U32.add i a'.array_offset;
        array_length = U32.sub a'.array_length i;
      }) in
    let split_h_1, split_h_2 = split_array_heaps a iseq p i pre h in
    split_array_heaps_disjoint a iseq p i pre h;
    split_array_heaps_joint_equal a iseq p i pre h;
    (| (a1, a2), h  |)
#pop-options

#push-options "--ifuel 1 --fuel 2 --z3rlimit 30"
let split_array_action
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: perm{readable p})
  (i:U32.t{U32.v i < U32.v (length a)})
  (pre: Ghost.erased (Preorder.preorder (option t)))
  : action
    (pts_to_array_with_preorder a p iseq pre)
    (as:(array_ref t & array_ref t){
      length (fst as) = i /\ length (snd as) = U32.sub (length a) i /\
      (not (is_null_array a) ==>
        (U32.v i > 0 ==> address (fst as) = address a /\ max_length (fst as) = max_length a /\
          offset (fst as) = offset a) /\
        (U32.v i < U32.v (length a) ==> address (snd as) = address a /\
          max_length (snd as) = max_length a /\ offset (snd as) = U32.add (offset a) i)
      )
    })
    (fun (a1, a2) -> star
      (pts_to_array_with_preorder a1 p (Seq.slice iseq 0 (U32.v i)) pre)
      (pts_to_array_with_preorder a2 p (Seq.slice iseq (U32.v i) (U32.v (length a))) pre)
    )
  =
  pre_action_to_action
    (split_array_pre_action a iseq p i pre)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 -> ())
    (fun h0 addr -> ())
#pop-options

let split_array
  (#t: _)
  (uses:Set.set lock_addr)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: perm{readable p})
  (i:U32.t{U32.v i < U32.v (length a)})
  : atomic
    uses
    false
    (pts_to_array a p iseq)
    (as:(array_ref t & array_ref t){
      length (fst as) = i /\ length (snd as) = U32.sub (length a) i /\
      (not (is_null_array a) ==>
        (U32.v i > 0 ==> address (fst as) = address a /\ max_length (fst as) = max_length a /\
          offset (fst as) = offset a) /\
        (U32.v i < U32.v (length a) ==> address (snd as) = address a /\
          max_length (snd as) = max_length a /\ offset (snd as) = U32.add (offset a) i)
      )
    })
    (fun (a1, a2) -> star
      (pts_to_array a1 p (Seq.slice iseq 0 (U32.v i)))
      (pts_to_array a2 p (Seq.slice iseq (U32.v i) (U32.v (length a))))
    )
  =
  promote_action
    uses
    false
    (split_array_action a iseq p i (trivial_optional_preorder (trivial_preorder t)))
    (fun h addr -> ())

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 30"
let glue_array_pre_action
  (#t: _)
  (a: array_ref t)
  (a': array_ref t{
    ((not (is_null_array a) /\ not (is_null_array a')) ==> address a = address a') /\
    max_length a = max_length a' /\
    offset a' = U32.add (offset a) (length a)
  })
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (iseq': Ghost.erased (Seq.lseq t (U32.v (length a'))))
  (p: perm{readable p})
  (pre: Ghost.erased (Preorder.preorder (option t)))
  : pre_action
    (star (pts_to_array_with_preorder a p iseq pre) (pts_to_array_with_preorder a' p iseq' pre))
    (new_a:array_ref t{
      max_length new_a = max_length a /\
      offset new_a = offset a /\ length new_a = U32.add (length a) (length a') /\
      (not (is_null_array a) ==> address new_a = address a)
    })
    (fun new_a -> pts_to_array_with_preorder new_a p (Seq.Base.append iseq iseq') pre)
  = fun h -> match a with
  | None -> (| a', h |)
  | Some a -> begin match a' with
    | None -> (| Some a, h |)
    | Some a' ->
    let new_a : array_ref t =
      Some ({ a with array_length = U32.add a.array_length a'.array_length})
    in
    (| new_a, h |)
  end
#pop-options

#push-options "--initial_ifuel 1 --max_ifuel 1"
let glue_array_action
  (#t: _)
  (a: array_ref t)
  (a': array_ref t{
    ((not (is_null_array a) /\ not (is_null_array a')) ==> address a = address a') /\
    max_length a = max_length a' /\
    offset a' = U32.add (offset a) (length a)
  })
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (iseq': Ghost.erased (Seq.lseq t (U32.v (length a'))))
  (p: perm{readable p})
  (pre: Ghost.erased (Preorder.preorder (option t)))
  : action
    (star (pts_to_array_with_preorder a p iseq pre) (pts_to_array_with_preorder a' p iseq' pre))
    (new_a:array_ref t{
      max_length new_a = max_length a /\
      offset new_a = offset a /\ length new_a = U32.add (length a) (length a') /\
      (not (is_null_array a) ==> address new_a = address a)
    })
    (fun new_a -> pts_to_array_with_preorder new_a p (Seq.Base.append iseq iseq') pre)
  =
  pre_action_to_action
    (glue_array_pre_action a a' iseq iseq' p pre)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 -> ())
    (fun h0 addr -> ())
#pop-options

let glue_array
  (#t: _)
  (uses:Set.set lock_addr)
  (a: array_ref t)
  (a': array_ref t{
    ((not (is_null_array a) /\ not (is_null_array a')) ==> address a = address a') /\
    max_length a = max_length a' /\
    offset a' = U32.add (offset a) (length a)
  })
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (iseq': Ghost.erased (Seq.lseq t (U32.v (length a'))))
  (p: perm{readable p})
  : atomic
    uses
    false
    (star (pts_to_array a p iseq) (pts_to_array a' p iseq'))
    (new_a:array_ref t{
      max_length new_a = max_length a /\
      offset new_a = offset a /\ length new_a = U32.add (length a) (length a') /\
      (not (is_null_array a) ==> address new_a = address a)
    })
    (fun new_a -> pts_to_array new_a p (Seq.Base.append iseq iseq'))
  =
  promote_action
    uses
    false
    (glue_array_action a a' iseq iseq' p (trivial_optional_preorder (trivial_preorder t)))
    (fun h addr -> ())


///////////////////////////////////////////////////////////////////////////////
// References
///////////////////////////////////////////////////////////////////////////////

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let sel_ref_heap
  (#t: Type0)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (h: hheap (ref r))
  : t =
  assert(exists (p:perm{readable p}) (contents: Ghost.erased t).
    interp_heap (pts_to_ref r p contents) h
  );
  let Array t' len' seq live = select_addr h (Some?.v r).array_addr in
  let x =  select_index seq 0 in
  x.value
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let sel_ref
  (#t: Type0)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (m: hmem (ref r))
  : t =
  assert(exists (p:perm{readable p}) (contents: Ghost.erased t).
    interp (pts_to_ref r p contents) m
  );
  let Array t' len' seq live = select_addr (heap_of_mem m) (Some?.v r).array_addr in
  let x =  select_index seq 0 in
  x.value
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --initial_fuel 1 --max_fuel 1"
let sel_ref_lemma
  (#t: Type0)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (p: perm{readable p})
  (m: hmem (ref_perm r p))
  : Lemma (
    interp (ref r) m /\
    interp (pts_to_ref r p (sel_ref r m)) m
  )
  =
  affine_star (ref r) (locks_invariant Set.empty m) m;
  assert(exists (p:perm{readable p}) (contents: Ghost.erased t).
    interp (pts_to_ref r p contents) m
  )
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --initial_fuel 1 --max_fuel 1"
let sel_ref_lemma_heap
  (#t: Type0)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (p: perm{readable p})
  (m: hheap (ref_perm r p))
  : Lemma (
    interp_heap (ref r) m /\
    interp_heap (pts_to_ref r p (sel_ref_heap r m) ) m
  )
  =
  assert(exists (p:perm{readable p}) (contents: Ghost.erased t).
    interp_heap (pts_to_ref r p contents) m
  )
#pop-options

#push-options "--z3rlimit 10"
let sel_ref_depends_only_on #a #pre r p m0 m1 = ()
#pop-options

let get_ref_pre_action
  (#t: Type0)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (p: perm{readable p})
  : pre_action
    (ref_perm r p)
    (x:t)
    (fun x -> pts_to_ref r p x)
  = fun h ->
  let contents = sel_ref_heap r h in
  sel_ref_lemma_heap r p h;
  let (| x, h' |) =
    index_array_pre_action r (Seq.create 1 contents) 0ul p (trivial_optional_preorder pre) h
  in
  (| x, h' |)


#push-options "--z3rlimit 50 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let get_ref_action
  (#t: Type0)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (p: perm{readable p})
  : action
    (ref_perm r p)
    (x:t)
    (fun x -> pts_to_ref r p x)
  =
  pre_action_to_action
    (get_ref_pre_action r p)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1  -> ())
    (fun h0 addr -> ())
#pop-options

let get_ref
  (#t: Type0)
  (uses:Set.set lock_addr)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (p: perm{readable p})
  : atomic
    uses
    false
    (ref_perm r p)
    (x:t)
    (fun x -> pts_to_ref r p x)
  =
  promote_action
    uses
    false
    (get_ref_action r p)
    (fun h0 addr -> ())

#push-options "--max_fuel 2 --initial_fuel 2"
let set_ref_pre_action
  (#t: Type0)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (old_v: Ghost.erased t)
  (v: t{pre old_v v})
  : pre_action
    (pts_to_ref r full_perm old_v)
    unit
    (fun _ -> pts_to_ref r full_perm v)
  = fun h ->
  let contents = sel_ref_heap r h in
  sel_ref_lemma_heap r full_perm h;
  assert(Seq.upd (Seq.create 1 contents) 0 v `Seq.equal` Seq.create 1 v);
  upd_array_pre_action r (Seq.create 1 contents) 0ul v (trivial_optional_preorder pre) h
#pop-options

#push-options "--fuel 2 --z3rlimit 30"
let set_ref_action
  (#t: Type0)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (old_v: Ghost.erased t)
  (v: t{pre old_v v})
  : action
    (pts_to_ref r full_perm old_v)
    unit
    (fun _ -> pts_to_ref r full_perm v)
  =
  pre_action_to_action
    (set_ref_pre_action r old_v v)
     (fun frame h0 h1 addr -> (* Disjointness preservation *)
     sel_ref_lemma_heap r full_perm h0;
     let iseq = Seq.create 1 (sel_ref_heap r h0) in
      upd_array_heap_frame_disjointness_preservation r iseq 0ul v (trivial_optional_preorder pre)
        (join_heap h0 h1) h0 h1 frame
    )
    (fun frame h0 h1 addr -> (* Does not depend on framing *)
      sel_ref_lemma_heap r full_perm h0;
      let iseq = Seq.create 1 (sel_ref_heap r h0) in
      upd_array_action_memory_split_independence r iseq 0ul v (trivial_optional_preorder pre)
        (join_heap h0 h1) h0 h1 frame
    )
    (fun frame h0 h1  -> (* Return and post *)
      let iseq = Seq.create 1 (sel_ref_heap r h0) in
      sel_ref_lemma_heap r full_perm h0;
      let (| x0, h |) = set_ref_pre_action r old_v v h0 in
      let (| x1, h' |) = set_ref_pre_action r old_v v (join_heap h0 h1) in
      assert (x0 == x1)
    )
    (fun h0 addr -> ())
#pop-options

let set_ref
  (#t: Type0)
  (uses:Set.set lock_addr)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (old_v: Ghost.erased t)
  (v: t{pre old_v v})
  : atomic
    uses
    false
    (pts_to_ref r full_perm old_v)
    unit
    (fun _ -> pts_to_ref r full_perm v)
  =
  promote_action
    uses
    false
    (set_ref_action r old_v v)
    (fun h0 addr -> ())

let alloc_ref
  (#t: Type0)
  (v: t)
  (pre: Ghost.erased (Preorder.preorder t))
  : m_action
    emp
    (reference t pre)
    (fun r -> pts_to_ref r full_perm v)
  =
  alloc_array_is_m_frame_and_preorder_preserving 1ul v (trivial_optional_preorder pre);
  alloc_array_pre_m_action 1ul v (trivial_optional_preorder pre)

#push-options "--ifuel 1 --fuel 2 --z3rlimit 30"
let free_ref_pre_action
  (#t: Type0)
  (#pre: Preorder.preorder t)
  (a: reference t pre)
  : pre_action
    (ref_perm a full_perm)
    unit
    (fun _ -> emp)
  =
  fun h -> (| (), on _ (fun a' ->
    let a_t = Some?.v a in
    if a_t.array_addr <> a' then h a' else match h a' with
    | Some (Array t' len seq live) ->
      assert(t' == t');
      let aux (i:nat{i < len}) : Lemma (
        Some? (Seq.index seq i).v_with_p /\
        (Some?.v (Seq.index seq i).v_with_p).perm == full_perm
      ) =
        assert(exists (contents: Ghost.erased (Seq.lseq t (U32.v (length a))))
          (pre: Preorder.preorder (option t)).
          interp_heap (pts_to_array_with_preorder a full_perm contents pre) h
        );
        let pf: squash (exists (contents: Ghost.erased (Seq.lseq t (U32.v (length a)))). (
          exists (pre: Preorder.preorder (option t)).
            interp_heap (pts_to_array_with_preorder a full_perm contents pre) h
          )
        ) = () in
        Classical.exists_elim
          (Some? (Seq.index seq i).v_with_p /\
            (Some?.v (Seq.index seq i).v_with_p).perm == full_perm)
          pf (fun contents ->
            let pf : squash (exists (pre: Preorder.preorder (option t)).
            interp_heap (pts_to_array_with_preorder a full_perm contents pre) h
            ) = () in
            Classical.exists_elim
              (Some? (Seq.index seq i).v_with_p /\
                (Some?.v (Seq.index seq i).v_with_p).perm == full_perm)
              pf (fun pre ->
                assert(interp_heap (pts_to_array_with_preorder a full_perm contents pre) h);
                assert(contains_index seq i);
                let x = select_index seq i in
                assert(full_perm `lesser_equal_perm` x.perm)
              )
        )
      in
      Classical.forall_intro aux;
      assert(all_full_permission seq);
      Some (Array t len seq false)
    | _ -> h a'
  )|)
#pop-options

#push-options "--ifuel 1 --fuel 2 --z3rlimit 50"
let free_ref_action
  (#t: Type0)
  (#pre: Preorder.preorder t)
  (a: reference t pre)
  : action
    (ref_perm a full_perm)
    unit
    (fun _ -> emp)
  =
  pre_action_to_action
    (free_ref_pre_action a)
    (fun frame h0 h1 addr ->
      let a' = Some?.v a in
      let (| _, h0' |) = free_ref_pre_action a h0 in
      if addr <> a'.array_addr then () else
      match h0' addr, h1 addr with
      | Some (Array t0 len0 seq0 live0), Some (Array t1 len1 seq1 live1) ->
        assert(not live0)
      | _ -> ()
    )
    (fun frame h0 h1 addr ->
      let (| _, h0' |) = free_ref_pre_action a h0 in
      let (|_, h'|) = free_ref_pre_action a (join_heap h0 h1) in
      match h' addr, h0' addr, h1 addr, (join_heap h0' h1) addr with
      | Some (Array t' len' seq' live'), Some (Array t0' len0' seq0' live0'),
        Some (Array t1 len1 seq1 live1), Some (Array tj lenj seqj livej) ->
        assert(exists (contents: Ghost.erased (Seq.lseq t (U32.v (length a))))
          (pre: Preorder.preorder (option t)).
          interp_heap (pts_to_array_with_preorder a full_perm contents pre) h0
        );
        let pf: squash (exists (contents: Ghost.erased (Seq.lseq t (U32.v (length a)))). (
          exists (pre: Preorder.preorder (option t)).
            interp_heap (pts_to_array_with_preorder a full_perm contents pre) h0
          )
        ) = () in
        Classical.exists_elim
          (h' addr == (join_heap h0' h1) addr)
          pf (fun contents ->
            let pf : squash (exists (pre: Preorder.preorder (option t)).
            interp_heap (pts_to_array_with_preorder a full_perm contents pre) h0
            ) = () in
            Classical.exists_elim
              (h' addr == (join_heap h0' h1) addr)
              pf (fun pre ->
                assert(seq' `Seq.equal` seqj)
              )
          )
      | _ -> ()
    )
    (fun frame h0 h1  -> ())
    (fun h0 addr -> ())
#pop-options

let free_ref
  (#t: Type0)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  : m_action
    (ref_perm r full_perm)
    unit
    (fun _ -> emp)
  =
  non_alloc_action_to_non_locking_m_action
    (free_ref_action r)
    (fun h0 addr -> ())

#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
let share_ref_pre_action
  (#t: Type0)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (p: perm{readable p})
  (contents: Ghost.erased t)
  : pre_action
    (pts_to_ref r p contents)
    (r':reference t pre{ref_address r' = ref_address r})
    (fun r' ->
      pts_to_ref r (half_perm p) contents `star`
      pts_to_ref r' (half_perm p) contents
    )
  = fun h ->
      let iseq = Ghost.hide (Seq.create 1 (Ghost.reveal contents)) in
      let (| x, h' |) = share_array_pre_action r iseq p (trivial_optional_preorder pre) h in
      (| x, h' |)
#pop-options

let share_ref_action
  (#t: _)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (p: perm{readable p})
  (contents: Ghost.erased t)
  : action
    (pts_to_ref r p contents)
    (r':reference t pre{ref_address r' = ref_address r})
    (fun r' ->
      pts_to_ref r (half_perm p) contents `star`
      pts_to_ref r' (half_perm p) contents
    )
  =
  pre_action_to_action
    (share_ref_pre_action r p contents)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 -> ())
    (fun h0 addr -> ())

let share_ref
  (#t: Type0)
  (uses:Set.set lock_addr)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (p: perm{readable p})
  (contents: Ghost.erased t)
  : atomic
    uses
    false
    (pts_to_ref r p contents)
    (r':reference t pre{ref_address r' = ref_address r})
    (fun r' ->
      pts_to_ref r (half_perm p) contents `star`
      pts_to_ref r' (half_perm p) contents
    )
  =
  promote_action
    uses
    false
    (share_ref_action r p contents)
    (fun h addr -> ())
#pop-options

let gather_ref
  (#t: Type0)
  (uses:Set.set lock_addr)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (r':reference t pre{ref_address r' = ref_address r})
  (p: perm{readable p})
  (p': perm{readable p'})
  (contents: Ghost.erased t)
  : atomic
    uses
    false
    (pts_to_ref r p contents `star` pts_to_ref r' p' contents)
    unit
    (fun _ -> pts_to_ref r (sum_perm p p') contents)
  =
  promote_action
    uses
    false
    (gather_array_action r r' (Seq.create 1 (Ghost.reveal contents)) p p' (trivial_optional_preorder pre))
    (fun h addr -> ())

let get_ref_refine_injective_hprop
  (#t: Type0)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (p: perm{readable p})
  (q:t -> hprop)
  (h:heap)
  : Lemma
  (requires
    interp_heap (h_exists (fun (v:t) -> pts_to_ref r p v `star` q v)) h)
  (ensures
    interp_heap (ref r) h /\
    interp_heap (pts_to_ref r p (sel_ref_heap r h) `star` q (sel_ref_heap r h)) h)
  =
  let open FStar.IndefiniteDescription in
  let (|v, _ |) = indefinite_description t
      (fun v -> interp_heap (pts_to_ref r p v `star` q v) h) in
  sel_ref_lemma_heap r p h;
  let contents = sel_ref_heap r h in
  affine_star_heap (pts_to_ref r p v) (q v) h;
  assert (interp_heap (pts_to_ref r p v) h);
  assert (interp_heap (pts_to_ref r p contents) h);
  assert (v == contents)

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let get_ref_refine_pre_action
  (#t: Type0)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (p: perm{readable p})
  (q:t -> hprop)
  : pre_action
    (h_exists (fun (v:t) -> pts_to_ref r p v `star` q v))
    (x:t)
    (fun v -> pts_to_ref r p v `star` q v)
  = fun h ->
    get_ref_refine_injective_hprop r p q h;
    let contents = sel_ref_heap r h in
    sel_ref_lemma_heap r p h;
    assert (interp_heap (pts_to_ref r p contents `star` q contents) h);
    let x = read_array_addr r (Seq.create 1 contents) 0ul p (trivial_optional_preorder pre) h in
    (| x, h |)

#restart-solver

let get_ref_refine_does_not_depend_on_framing
  (#t: Type0)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (p: perm{readable p})
  (q: t -> hprop)
  (frame: hprop)
  (h0: hheap (h_exists (fun (v:t) -> pts_to_ref r p v `star` q v)))
  (h1: hheap frame{disjoint_heap h0 h1})
  : Lemma (
      let (|x_alone, h0'|) = (get_ref_refine_pre_action r p q) h0 in
      let (|x_joint, h'|) = (get_ref_refine_pre_action r p q) (join_heap h0 h1) in
      x_alone == x_joint
    )
  =
    sel_ref_lemma_heap r p h0;
    let h' = join_heap h0 h1 in
    let r = Some?.v r in
    assert (disjoint_addr h0 h1 r.array_addr);
    assert (Some? (h0 r.array_addr) /\ Array? (Some?.v (h0 r.array_addr)));
    assert (Some? (h' r.array_addr) /\ Array? (Some?.v (h' r.array_addr)));
    let a1 = Some?.v (h0 r.array_addr) in
    let a2 = Some?.v (h' r.array_addr) in
    let Array t1 len1 seq1 live1 = a1 in
    let Array t2 len2 seq2 live2 = a2 in
    let v1 = Seq.index seq1 (U32.v r.array_offset + U32.v 0ul) in
    let v2 = Seq.index seq2 (U32.v r.array_offset + U32.v 0ul) in
    let x1 = Some?.v v1.v_with_p in
    let x2 = Some?.v v2.v_with_p in
    assert (x1.value == x2.value)
#pop-options

#push-options "--z3rlimit 50 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let get_ref_refine_action
  (#t: Type0)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (p: perm{readable p})
  (q:t -> hprop)
  : action
    (h_exists (fun (v:t) -> pts_to_ref r p v `star` q v))
    (x:t)
    (fun v -> pts_to_ref r p v `star` q v)
  =
  pre_action_to_action
    (get_ref_refine_pre_action r p q)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (get_ref_refine_does_not_depend_on_framing r p q)
    (fun h0 addr -> ())
#pop-options

let get_ref_refine
  (#t:Type0)
  (uses:Set.set lock_addr)
  (#pre:Preorder.preorder t)
  (r:reference t pre)
  (p:perm{readable p})
  (q:t -> hprop)
  : atomic
    uses
    false
    (h_exists (fun (v:t) -> pts_to_ref r p v `star` q v))
    (x:t)
    (fun v -> pts_to_ref r p v `star` q v)
  =
  promote_action
    uses
    false
    (get_ref_refine_action r p q)
    (fun h0 addr -> ())

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let cas_pre_action
  (#t:eqtype)
  (#pre:Preorder.preorder t)
  (r:reference t pre)
  (v:Ghost.erased t)
  (v_old:t)
  (v_new:t{pre v v_new})
  : pre_action
    (pts_to_ref r full_perm v)
    (b:bool{b <==> (Ghost.reveal v == v_old)})
    (fun b -> if b then pts_to_ref r full_perm v_new else pts_to_ref r full_perm v)
  = fun h ->
      let contents = sel_ref_heap r h in
      if v_old <> contents then (| false, h |)
      else (
        let res = set_ref_pre_action r v v_new h in
        let h' = dsnd res in
        (| true, h' |)
     )
#pop-options

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let cas_preserves_frame_disjointness_addr
  (#t:eqtype)
  (#pre:Preorder.preorder t)
  (r:reference t pre)
  (v:Ghost.erased t)
  (v_old:t)
  (v_new:t{pre v v_new})
  (frame: hprop)
  (h0:hheap (pts_to_ref r full_perm v))
  (h1:hheap frame{disjoint_heap h0 h1})
  (addr: addr)
  : Lemma (
      let (|_, h0'|) = cas_pre_action r v v_old v_new h0 in
      disjoint_addr h0' h1 addr
    )
  = sel_ref_lemma_heap r full_perm h0;
    let iseq = Seq.create 1 (sel_ref_heap r h0) in
    upd_array_heap_frame_disjointness_preservation r iseq 0ul v_new (trivial_optional_preorder pre)
      (join_heap h0 h1) h0 h1 frame
#pop-options

#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"
let cas_does_not_depend_on_framing_addr
  (#t:eqtype)
  (#pre:Preorder.preorder t)
  (r:reference t pre)
  (v:Ghost.erased t)
  (v_old:t)
  (v_new:t{pre v v_new})
  (frame: hprop)
  (h0:hheap (pts_to_ref r full_perm v))
  (h1:hheap frame{disjoint_heap h0 h1})
  (addr: addr)
  : Lemma (requires (
      let (|_, h0'|) = cas_pre_action r v v_old v_new h0 in
      disjoint_heap h0' h1
    ))
    (ensures (
      let (|_, h0'|) = cas_pre_action r v v_old v_new h0 in
      let (|_, h'|) = cas_pre_action r v v_old v_new (join_heap h0 h1) in
      h' addr == join_heap h0' h1 addr
    ))
  = sel_ref_lemma_heap r full_perm h0;
    let iseq = Seq.create 1 (sel_ref_heap r h0) in
    upd_array_action_memory_split_independence r iseq 0ul v_new (trivial_optional_preorder pre)
      (join_heap h0 h1) h0 h1 frame
#pop-options

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let cas_result_does_not_depend_on_framing
  (#t:eqtype)
  (#pre:Preorder.preorder t)
  (r:reference t pre)
  (v:Ghost.erased t)
  (v_old:t)
  (v_new:t{pre v v_new})
  (frame: hprop)
  (h0:hheap (pts_to_ref r full_perm v))
  (h1:hheap frame{disjoint_heap h0 h1})
  : Lemma (
      let (|x_alone, h0'|) = cas_pre_action r v v_old v_new h0 in
      let (|x_joint, h'|) = cas_pre_action r v v_old v_new (join_heap h0 h1) in
      x_alone == x_joint
    )
  = sel_ref_lemma_heap r full_perm h0;
    let iseq = Seq.create 1 (sel_ref_heap r h0) in
    let (| x0, h |) = set_ref_pre_action r v v_new h0 in
    let (| x1, h' |) = set_ref_pre_action r v v_new (join_heap h0 h1) in
    assert (x0 == x1)
#pop-options

let cas_action
  (#t:eqtype)
  (#pre:Preorder.preorder t)
  (r:reference t pre)
  (v:Ghost.erased t)
  (v_old:t)
  (v_new:t{pre v v_new})
  : action
    (pts_to_ref r full_perm v)
    (b:bool{b <==> (Ghost.reveal v == v_old)})
    (fun b -> if b then pts_to_ref r full_perm v_new else pts_to_ref r full_perm v)
  =
  pre_action_to_action
    (cas_pre_action r v v_old v_new)
    (cas_preserves_frame_disjointness_addr r v v_old v_new)
    (cas_does_not_depend_on_framing_addr r v v_old v_new)
    (cas_result_does_not_depend_on_framing r v v_old v_new)
    (fun h0 addr -> ())

let cas
  (#t:eqtype)
  (uses:Set.set lock_addr)
  (#pre:Preorder.preorder t)
  (r:reference t pre)
  (v:Ghost.erased t)
  (v_old:t)
  (v_new:t{pre v v_new})
  : atomic
    uses
    false
    (pts_to_ref r full_perm v)
    (b:bool{b <==> (Ghost.reveal v == v_old)})
    (fun b -> if b then pts_to_ref r full_perm v_new else pts_to_ref r full_perm v)
  =
  promote_action
    uses
    false
    (cas_action r v v_old v_new)
    (fun h0 addr ->
      assert(h0 addr == None);
      let (| _ , h1 |) = cas_pre_action r v v_old v_new h0 in
      assert(h1 addr == None)
    )

#push-options "--fuel 3 --ifuel 0"
let reference_preorder_respected
  (#t: Type0)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (m0 m1:mem)
  : Lemma
    (requires (interp (ref r) m0 /\ interp (ref r) m1 /\ mem_evolves m0 m1))
    (ensures (pre (sel_ref r m0) (sel_ref r m1)))
  =
  assert(heap_evolves m0.heap m1.heap);
  assert(heap_evolves_addr m0.heap m1.heap (Some?.v r).array_addr);
  let addr = (Some?.v r).array_addr in
  match m0.heap addr, m1.heap addr with
  | Some (Array t0 len0 seq0 live0), Some (Array t1 len1 seq1 live1) ->
    assert(heap_evolves_seq seq0 seq1 0)
  | _ -> ()
#pop-options
