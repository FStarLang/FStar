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
open Steel.Permissions
open Steel.Memory
module U32 = FStar.UInt32
open FStar.FunctionalExtensionality

friend Steel.Memory

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

let hprop_of_lock_state (l:lock_state) : hprop =
  match l with
  | Available p -> p
  | Locked p -> p
  | Invariant p -> p

module L = FStar.List.Tot

assume
val get_lock (l:lock_store) (i:nat{i < L.length l})
  : (prefix : lock_store &
     li : lock_state &
     suffix : lock_store {
       l == L.(prefix @ (li::suffix)) /\
       L.length (li::suffix) == i + 1
     })

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

let mem_evolves : Preorder.preorder mem =
  fun m0 m1 -> lock_store_evolves m0.locks m1.locks

let lock_store_unchanged_respects_preorder (m0 m1: mem) : Lemma
  (requires (m0.locks == m1.locks))
  (ensures (mem_evolves m0 m1))
  =
  ()

let pre_action (fp:hprop) (a:Type) (fp':a -> hprop) =
  hheap fp -> (x:a & hheap (fp' x))

let is_frame_preserving (#a:Type) (#fp:hprop) (#fp':a -> hprop) (f:pre_action fp a fp') =
  forall (frame:hprop) (h0:heap).
    interp (fp `star` frame) h0 ==>
    (let (| x, h1 |) = f h0 in
     interp (fp' x `star` frame) h1 /\
     (forall (f_frame:fp_prop frame). f_frame h0 <==> f_frame h1))

let action (fp:hprop) (a:Type) (fp':a -> hprop) =
  f:pre_action fp a fp'{ is_frame_preserving f }


#push-options "--max_fuel 2 --initial_ifuel 2"
let is_frame_preserving_intro
  (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_action fp a fp')
  (preserves_framing_intro:
    (frame: hprop) -> (h0: heap) ->
    Lemma (requires (interp (fp `star` frame) h0)) (ensures (
      let (| x, h1 |) = f h0 in  interp (fp' x `star` frame) h1
    ))
  )
  (preserves_frame_prop_intro:
    (frame: hprop) -> (h0: heap) ->
    (f_frame: fp_prop frame) ->
    Lemma (requires (interp (fp `star` frame) h0)) (ensures (
      let (| x, h1 |) = f h0 in f_frame h0 <==> f_frame h1
    ))
  )
  : Lemma (is_frame_preserving f)
  =
  let aux (frame: hprop) (h0: heap) : Lemma (interp (fp `star` frame) h0 ==>
     (let (| x, h1 |) = f h0 in
     interp (fp' x `star` frame) h1 /\
     (forall (f_frame:fp_prop frame). f_frame h0 <==> f_frame h1))
  ) =
    let aux (pf: (interp (fp `star` frame) h0)) : Lemma (
      interp (fp `star` frame) h0 /\ (
      let h0 : (h0:heap{interp fp h0}) = affine_star fp frame h0; h0 in
      let (| x, h1 |) = f h0 in
      interp (fp' x `star` frame) h1 /\
      (forall (f_frame:fp_prop frame). f_frame h0 <==> f_frame h1))
    ) =
      affine_star fp frame h0;
      let (| x, h1 |) = f h0 in
      let aux (f_frame:fp_prop frame)
        : Lemma (f_frame h0 <==> f_frame h1) =
        preserves_frame_prop_intro frame h0 f_frame
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
  (f_frame:fp_prop frame)
  : Lemma (requires (is_frame_preserving f /\ interp (fp `star` frame) h0)) (ensures (
     let (| x, h1 |) = f h0 in
     interp (fp' x `star` frame) h1 /\
     f_frame h0 <==> f_frame h1
  ))
  = ()

let depends_only_on_without_affinity_elim
  (q:heap -> prop) (fp:hprop)
  (h0:hheap fp)
  (h1:heap{disjoint h0 h1})
  : Lemma
    (requires (depends_only_on_without_affinity q fp))
    (ensures (q h0 <==> q (join h0 h1)))
  = ()

#push-options "--z3rlimit 100 --max_fuel 1 --initial_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let pre_action_to_action
  (fp:hprop) (a: Type) (fp': a -> hprop) (f: pre_action fp a fp')
  (action_preserves_frame_disjointness_addr:
    (frame: hprop) ->
    (h0:hheap fp) ->
    (h1:hheap frame{disjoint h0 h1}) ->
    (addr: addr) ->
    Lemma (
      let (|_, h0'|) = f h0 in
      disjoint_addr h0' h1 addr
    )
  )
  (action_does_not_depend_on_framing_addr:
    (frame: hprop) ->
    (h0:hheap fp) ->
    (h1:hheap frame{disjoint h0 h1}) ->
    (addr: addr) ->
    Lemma (requires (
      let (|_, h0'|) = f h0 in
      disjoint h0' h1
    ))
    (ensures (
      let (|_, h0'|) = f h0 in
      let (|_, h'|) = f (join h0 h1) in
      h' addr == join h0' h1 addr
    ))
  )
  (action_result_does_not_depend_on_framing:
    (frame: hprop) ->
    (h0:hheap fp) ->
    (h1:hheap frame{disjoint h0 h1}) ->
    Lemma (
      let (|x_alone, h0'|) = f h0 in
      let (|x_joint, h'|) = f (join h0 h1) in
      x_alone == x_joint
    )
  )
  : Tot (action fp a fp')
  =
  is_frame_preserving_intro f (fun frame h ->
    let (| x, h' |) = f h in
    let pf :squash (exists (h0:heap). (exists (h1:heap).
      disjoint h0 h1 /\ h == join h0 h1 /\ interp fp h0 /\ interp frame h1
    )) =
      assert(interp (fp `star` frame) h)
    in
    Classical.exists_elim
      (interp (fp' x `star` frame) h') pf
      (fun h0 ->
        let pf: squash (exists (h1: hheap frame).
          disjoint h0 h1 /\ h == join h0 h1 /\ interp fp h0 /\ interp frame h1
        ) =
          ()
        in
        Classical.exists_elim
          (interp (fp' x `star` frame) h') pf
          (fun h1 ->
            let h0 : hheap fp = h0 in
            let h1 : (h1:hheap frame{disjoint h0 h1 /\ h == join h0 h1}) = h1 in
            let (|x_alone, h0'|) = f h0 in
            let (|x_joint, h'|) = f (join h0 h1) in
            let aux (addr: addr) : Lemma (disjoint_addr h0' h1 addr) =
              action_preserves_frame_disjointness_addr frame h0 h1 addr
            in
            Classical.forall_intro aux;
            let aux (addr: addr) : Lemma (h' addr == join h0' h1 addr) =
              action_does_not_depend_on_framing_addr frame h0 h1 addr
            in
            Classical.forall_intro aux;
            mem_equiv_eq h' (join h0' h1);
            assert(interp (fp' x_alone) h0');
            action_result_does_not_depend_on_framing frame h0 h1;
            assert(x_alone == x_joint);
            assert(interp frame h1);
            assert(h' == join h0' h1);
            assert(disjoint h0' h1);
            intro_star (fp' x) (frame) h0' h1;
            assert(interp (fp' x `star` frame) h')
        )
    )
  ) (fun frame h f_frame ->
    let (| x, h' |) = f h in
    let pf :squash (exists (h0:heap). (exists (h1:heap).
      disjoint h0 h1 /\ h == join h0 h1 /\ interp fp h0 /\ interp frame h1
    )) =
      assert(interp (fp `star` frame) h)
    in
    Classical.exists_elim
      (f_frame h <==> f_frame h') pf
      (fun h0 ->
        let pf: squash (exists (h1: hheap frame).
          disjoint h0 h1 /\ h == join h0 h1 /\ interp fp h0 /\ interp frame h1
        ) =
          ()
        in
        Classical.exists_elim
          (f_frame h <==> f_frame h') pf
          (fun h1 ->
           let h0 : hheap fp = h0 in
            let h1 : (h1:hheap frame{disjoint h0 h1 /\ h == join h0 h1}) = h1 in
            let (|x_alone, h0'|) = f h0 in
            let (|x_joint, h'|) = f (join h0 h1) in
            let aux (addr: addr) : Lemma (disjoint_addr h0' h1 addr) =
              action_preserves_frame_disjointness_addr frame h0 h1 addr
            in
            Classical.forall_intro aux;
            let aux (addr: addr) : Lemma (h' addr == join h0' h1 addr) =
              action_does_not_depend_on_framing_addr frame h0 h1 addr
            in
            Classical.forall_intro aux;
            mem_equiv_eq h' (join h0' h1);
              assert(f_frame `depends_only_on_without_affinity` frame);
              depends_only_on_without_affinity_elim f_frame frame h1 h0;
              assert(f_frame h1 <==> f_frame (join h1 h0));
              assert(join h1 h0 == h);
              depends_only_on_without_affinity_elim f_frame frame h1 h0';
              assert(join h1 h0' == h');
            assert(f_frame h <==> f_frame h')
          )
       )
  );
  f
#pop-options

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
    let (|x, h'|) = f m.heap in
    let aux (i: addr) : Lemma (requires (i >= m.ctr)) (ensures (h' i == None)) =
      non_alloc m.heap i
    in
    Classical.forall_intro (Classical.move_requires aux);
    let does_not_perturb_locks (lock_p: hprop) (h:hheap (fp `star` lock_p))
      : Lemma (let (|_, h'|) = f h in interp lock_p h') [SMTPat ()]
    =
      assert(is_frame_preserving f);
      assert(interp (fp `star` lock_p) h);
      let (| x, h' |) = f h in
      assert(interp (fp' x `star` lock_p) h');
      affine_star (fp' x) lock_p h';
      assert(interp lock_p h')
    in
    assert(interp (lock_store_invariant Set.empty m.locks) h');
    let m':mem = {m with heap = h'} in
    (| x, m' |)
#pop-options


#push-options "--warn_error -271 --max_fuel 1 --initial_fuel 1"
let alloc_action_to_non_locking_pre_m_action
  (fp:hprop) (a: Type) (fp': a -> hprop) (f: action fp a fp')
  (alloc_lemma: (h: hheap fp) -> (alloc_addr: addr) -> Lemma
    (forall (a: addr). let (| _, h'|) = f h in
      h a == None ==> (if a = alloc_addr then h' a =!= None else h' a == None)
    )
  )
  : Tot (pre_m_action fp a fp')
  =
  fun m ->
    let (|x, h'|) = f m.heap in
    let aux (i: addr) : Lemma (requires (i >= m.ctr + 1)) (ensures (h' i == None)) =
      alloc_lemma m.heap m.ctr
    in
    Classical.forall_intro (Classical.move_requires aux);
    let does_not_perturb_locks (lock_p: hprop) (h:hheap (fp `star` lock_p))
      : Lemma (let (|_, h'|) = f h in interp lock_p h') [SMTPat ()]
    =
      assert(is_frame_preserving f);
      assert(interp (fp `star` lock_p) h);
      let (| x, h' |) = f h in
      assert(interp (fp' x `star` lock_p) h');
      affine_star (fp' x) lock_p h';
      assert(interp lock_p h')
    in
    assert(interp (lock_store_invariant Set.empty m.locks) h');
    let m':mem = {m with heap = h'; ctr = m.ctr + 1} in
    (| x, m' |)
#pop-options

#push-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let is_m_frame_and_preorder_preserving_intro_aux
  (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_m_action fp a fp')
  (preserves_framing_intro:
    (frame: hprop) -> (m0: hmem (fp `star` frame)) ->
    Lemma (ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
      let (| x, m1 |) = f m0 in
      interp ((fp' x `star` frame) `star` locks_invariant Set.empty m1) (heap_of_mem m1) /\
      mem_evolves m0 m1
    )
  )
  (frame_prop_preserves_intro:
    (frame: hprop) -> (m0: hmem (fp `star` frame)) -> (f_frame: fp_prop frame) ->
    Lemma (ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
      let (| x, m1 |) = f m0 in
      f_frame (heap_of_mem m0) <==> f_frame (heap_of_mem m1)
    )
  )
  (frame: hprop) (m0: hmem (fp `star` frame))
  : Lemma ((ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
      let (| x, m1 |) = f m0 in
      interp ((fp' x `star` frame) `star` locks_invariant Set.empty m1) (heap_of_mem m1) /\
      mem_evolves m0 m1 /\
      (forall (f_frame:fp_prop frame). f_frame (heap_of_mem m0) <==> f_frame (heap_of_mem m1))))
  =
   ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
    let (| x, m1 |) = f m0 in
    preserves_framing_intro frame m0;
    let aux (f_frame: fp_prop frame) : Lemma (
      f_frame (heap_of_mem m0) <==> f_frame (heap_of_mem m1)
    ) =
      frame_prop_preserves_intro frame m0 f_frame
    in
    Classical.forall_intro aux
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let is_m_frame_and_preorder_preserving_intro
  (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_m_action fp a fp')
  (preserves_framing_intro:
    (frame: hprop) -> (m0: hmem (fp `star` frame)) ->
    Lemma (ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
      let (| x, m1 |) = f m0 in
      interp ((fp' x `star` frame) `star` locks_invariant Set.empty m1) (heap_of_mem m1) /\
      mem_evolves m0 m1
    )
  )
  (frame_prop_preserves_intro:
    (frame: hprop) -> (m0: hmem (fp `star` frame)) -> (f_frame: fp_prop frame) ->
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

#push-options "--z3rlimit 50 --max_ifuel 1 --initial_ifuel 1 --max_fuel 2 --initial_fuel 2"
let non_alloc_action_to_non_locking_m_action
  (fp:hprop) (a: Type) (fp': a -> hprop) (f: action fp a fp')
    (non_alloc: (h: hheap fp) -> (addr: addr) -> Lemma
    (requires (h addr == None))
    (ensures (let (| _, h'|) = f h in h' addr == None))
  )
  : Tot (m_action fp a fp')
=
  let f_m = non_alloc_action_to_non_locking_pre_m_action fp a fp' f non_alloc in
  is_m_frame_and_preorder_preserving_intro f_m (fun frame m0 ->
    ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
    let (| x, m1 |) = f_m m0 in
    assert(locks_invariant Set.empty m0 == locks_invariant Set.empty m1);
    is_frame_preserving_elim f (frame `star` (locks_invariant Set.empty m0)) m0.heap (fun _ -> True);
    assert(interp (fp' x `star` (frame `star` locks_invariant Set.empty m1)) (heap_of_mem m1));
    star_associative (fp' x) frame (locks_invariant Set.empty m1);
    assert(interp ((fp' x `star` frame) `star` locks_invariant Set.empty m1) (heap_of_mem m1));
    lock_store_unchanged_respects_preorder m0 m1;
    assert(mem_evolves m0 m1)
  ) (fun frame m0 f_frame ->
    ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
    let (| x, m1 |) = f_m m0 in
    is_frame_preserving_elim f frame m0.heap f_frame;
    assert(f_frame (heap_of_mem m0) <==> f_frame (heap_of_mem m1))
  );
  f_m
#pop-options

/////////////////////////////////////////////////////////////////////////////
// Arrays
/////////////////////////////////////////////////////////////////////////////

#push-options "--max_fuel 3"
let as_seq (#t:_) (a:array_ref t) (m:hheap (array a)) =
  let Array t' len' seq = select_addr m a.array_addr in
  let len = U32.v a.array_length in
  assert(U32.v a.array_offset + U32.v a.array_length <= len');
  Seq.init len (fun i -> let x =  select_index seq (U32.v a.array_offset + i) in x.value)
#pop-options

#push-options "--max_fuel 2"
let as_seq_lemma
  (#t:_)
  (a:array_ref t)
  (i:U32.t{U32.v i < U32.v (length a)})
  (p:permission{allows_read p})
  (m:hheap (array_perm a p))
  =
  ()
#pop-options

let read_array_addr
  (#t: _)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i: U32.t{U32.v i < U32.v (length a)})
  (p:permission{allows_read p})
  (m: hheap (pts_to_array a p iseq))
  : Tot (x:t{x == Seq.index iseq (U32.v i)})
  =
  match m a.array_addr with
  | Some (Array t' len seq) ->
    assert(contains_index seq (U32.v a.array_offset + U32.v i));
    match Seq.index seq (U32.v a.array_offset + U32.v i) with
    | None -> ()
    | Some x -> x.value
  | _ -> ()

let index_array_pre_action
  (#t: _)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i: U32.t{U32.v i < U32.v (length a)})
  (p:permission{allows_read p})
  : Tot (pre_action
    (pts_to_array a p iseq)
    (x:t{x == Seq.index iseq (U32.v i)})
    (fun _ -> pts_to_array a p iseq))
  = fun h ->
  let x = read_array_addr a iseq i p h in
  (| x, h |)

let index_array_action
  (#t: _)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i: U32.t{U32.v i < U32.v (length a)})
  (p:permission{allows_read p})
  : Tot (pre_action
    (pts_to_array a p iseq)
    (x:t{x == Seq.index iseq (U32.v i)})
    (fun _ -> pts_to_array a p iseq))
  =
  pre_action_to_action
    (pts_to_array a p iseq)
    (x:t{x == Seq.index iseq (U32.v i)})
    (fun _ -> pts_to_array a p iseq)
    (index_array_pre_action a iseq i p)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 -> ())

let index_array
  (#t:_)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: permission{allows_read p})
  (i:U32.t{U32.v i < U32.v (length a)}) =
  non_alloc_action_to_non_locking_m_action
    (pts_to_array a p iseq)
    (x:t{x == Seq.index iseq (U32.v i)})
    (fun _ -> pts_to_array a p iseq)
    (index_array_action a iseq i p)
    (fun h addr -> ())

let update_array_addr
  (#t:_)
  (a: array_ref t)
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (perm:permission{allows_read perm})
  (m: heap{match m a.array_addr with
    | Some (Array t' len seq) ->
      t' == t /\ U32.v (offset a) + U32.v (length a) <= len
    | _ -> False
  })
  =
  match m a.array_addr with
  | Some (Array t' len seq) ->
    on _ (fun a' ->
      if a.array_addr = a' then
        let new_seq = Seq.upd seq (U32.v i + U32.v a.array_offset) (Some ({
          value = v; perm =  perm; preorder = trivial_preorder t
        })) in
        Some (Array t len new_seq)
      else
        m a'
    )
   | _ -> m

#push-options "--max_fuel 2 --initial_fuel 2"
let upd_array_heap
  (#t:_)
  (a:array_ref t)
  (iseq:  Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (h: hheap (pts_to_array a full_permission iseq)) : heap =
  let Array _ len v_orig = select_addr h a.array_addr in
  update_array_addr a i v full_permission h
#pop-options

#push-options "--z3rlimit 15 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let upd_array_heap_frame_disjointness_preservation
  (#t:_)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (h h0 h1:heap)
  (frame:hprop)
  : Lemma
    (requires
      disjoint h0 h1 /\
      h == join h0 h1 /\
      interp (pts_to_array a full_permission iseq) h0 /\
      interp frame h1)
    (ensures (
      let h0' = upd_array_heap a iseq i v h0 in
      disjoint h0' h1))
  =
  ()
#pop-options


let upd_array_pre_action
  (#t:_)
  (a:array_ref t)
  (iseq:  Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  : pre_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> pts_to_array a full_permission (Seq.upd iseq (U32.v i) v))
  = fun h ->
    (| (), upd_array_heap a iseq i v h |)

#push-options "--z3rlimit 150 --max_fuel 1 --initial_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let upd_array_action_memory_split_independence
  (#t:_)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (h h0 h1:heap)
  (frame:hprop)
  : Lemma
    (requires
      disjoint h0 h1 /\
      h == join h0 h1 /\
      interp (pts_to_array a full_permission iseq) h0 /\
      interp frame h1)
    (ensures (
      let (| _, h' |) = upd_array_pre_action a iseq i v h in
      let h0' = upd_array_heap a iseq i v h0 in
      upd_array_heap_frame_disjointness_preservation a iseq i v h h0 h1 frame;
      h' == (join h0' h1)))
  =
  let (| _, h' |) = upd_array_pre_action a iseq i v h in
  let h0' = upd_array_heap a iseq i v h0 in
  let aux (addr: addr) : Lemma (
    upd_array_heap_frame_disjointness_preservation a iseq i v h h0 h1 frame;
    assert(disjoint h0' h1);
    h' addr == (join h0' h1) addr
  ) =
    upd_array_heap_frame_disjointness_preservation a iseq i v h h0 h1 frame;
    if addr <> a.array_addr then () else
    if not (h1 `contains_addr` addr) then ()
    else match  h' addr, (join h0' h1) addr with
    | Some (Array t2 len2 seq2), Some (Array t3 len3 seq3) ->
      assert(seq2 `Seq.equal` seq3)
    | _ -> ()
  in
  Classical.forall_intro aux;
  mem_equiv_eq h' (join h0' h1)
#pop-options

let upd_array_action
  (#t:_)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  : Tot (
    action
      (pts_to_array a full_permission iseq)
      unit
      (fun _ -> pts_to_array a full_permission (Seq.upd iseq (U32.v i) v))
    )
  =
  pre_action_to_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> pts_to_array a full_permission (Seq.upd iseq (U32.v i) v))
    (upd_array_pre_action a iseq i v)
    (fun frame h0 h1 addr -> (* Disjointness preservation *)
      upd_array_heap_frame_disjointness_preservation a iseq i v (join h0 h1) h0 h1 frame
    )
    (fun frame h0 h1 addr -> (* Does not depend on framing *)
      upd_array_action_memory_split_independence a iseq i v (join h0 h1) h0 h1 frame
    )
    (fun frame h0 h1 -> (* Return  *)
      let (| x0, h |) = upd_array_pre_action a iseq i v h0 in
      let (| x1, h' |) = upd_array_pre_action a iseq i v (join h0 h1) in
      assert (x0 == x1)
    )

let upd_array
  (#t:_)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  : m_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> pts_to_array a full_permission (Seq.upd iseq (U32.v i) v))
  =
  non_alloc_action_to_non_locking_m_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> pts_to_array a full_permission (Seq.upd iseq (U32.v i) v))
    (upd_array_action a iseq i v)
    (fun h addr -> ())

// MST = MST mem locks_preorder

// let (:=) #a r v
// : action_t (ptr r) (fun _ -> points_to r v) (fun _ -> True)
//   (fun h0 _ h1 -> True)
//   let m = MST.get () in
//   let m1 = upd r v m in
//   MST.put m1

let singleton_heap
  (#t: _)
  (len:U32.t)
  (init: t)
  (a: array_ref t{
    U32.v len = U32.v a.array_length /\
    U32.v len = U32.v a.array_max_length /\
    0 = U32.v a.array_offset
  })
  : hheap (pts_to_array a full_permission (Seq.Base.create (U32.v len) init))
  =
  let h = on _ (fun a' ->
    if a' <> a.array_addr then None else
    Some (Array t (U32.v len) (Seq.init (U32.v len) (fun i ->
      Some ({
        value = init;
        perm = (full_permission <: (perm:permission{allows_read perm}));
        preorder = trivial_preorder t
      })
    )))
  ) in
  h


#push-options "--z3rlimit 50 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1 --warn_error -271"
let alloc_array_pre_m_action
  (#t: _)
  (len:U32.t)
  (init: t)
  : pre_m_action
    emp
    (a:array_ref t{length a = len /\ offset a = 0ul /\ max_length a = len})
    (fun a -> pts_to_array a full_permission (Seq.Base.create (U32.v len) init))
  =  fun m ->
  let a = {
    array_addr = m.ctr;
    array_max_length = len;
    array_length = len;
    array_offset = 0ul;
  } in
  let single_h = singleton_heap len init a in
  let new_h = join (heap_of_mem m) single_h in
  assert(forall i. i>= m.ctr + 1 ==> new_h i == None);
  assert(disjoint m.heap single_h);
  assert(interp (lock_store_invariant Set.empty m.locks) (heap_of_mem m));
  assert(interp (pts_to_array a full_permission (Seq.Base.create (U32.v len) init)) single_h);
  assert(interp ((pts_to_array a full_permission (Seq.Base.create (U32.v len) init))
    `star` (lock_store_invariant Set.empty m.locks)) new_h);
  let new_m = { m with heap = new_h; ctr = m.ctr +1 } in
  (| a, new_m |)
#pop-options

#restart-solver

let ac_reasoning_for_m_frame_preserving'
  (p q r:hprop) (m:mem)
: Lemma
  (requires interp ((p `star` q) `star` r) (heap_of_mem m))
  (ensures interp (q `star` r) (heap_of_mem m))
= calc (equiv) {
    (p `star` q) `star` r;
       (equiv) { star_associative p q r }
    p `star` (q `star` r);
  };
  assert (interp (p `star` (q `star` r)) (heap_of_mem m));
  affine_star p (q `star` r) (heap_of_mem m)


#push-options " --max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let alloc_array_is_m_frame_and_preorder_preserving
  (#t: _)
  (len:U32.t)
  (init: t)
  : Lemma (is_m_frame_and_preorder_preserving (alloc_array_pre_m_action len init))
  =
  is_m_frame_and_preorder_preserving_intro (alloc_array_pre_m_action len init) (fun frame m ->
    let h = heap_of_mem m in
    let a : array_ref t = {
      array_addr = m.ctr;
      array_max_length = len;
      array_length = len;
      array_offset = 0ul;
    } in
    ac_reasoning_for_m_frame_preserving emp frame (locks_invariant Set.empty m) m;
    let (| a, m1 |) = alloc_array_pre_m_action len init m in
    assert (m1.ctr = m.ctr + 1);
    assert (m1.locks == m.locks);
    let h1 = heap_of_mem m1 in
    let single_h = singleton_heap len init a in
    assert (h1 == join single_h h);
    intro_pts_to_array_with_preorder
      a full_permission (Seq.Base.create (U32.v len) init) (trivial_preorder t) single_h;
    assert (interp (pts_to_array a full_permission (Seq.Base.create (U32.v len) init)) single_h);
    ac_reasoning_for_m_frame_preserving' emp frame (locks_invariant Set.empty m) m;
    assert (interp (frame `star` locks_invariant Set.empty m) h);
    intro_star
      (pts_to_array a full_permission (Seq.Base.create (U32.v len) init))
      (frame `star` locks_invariant Set.empty m)
      single_h
      h;
    assert (interp
      (pts_to_array a full_permission (Seq.Base.create (U32.v len) init) `star`
      (frame `star` locks_invariant Set.empty m)) h1
    );
    star_associative
      (pts_to_array a full_permission (Seq.Base.create (U32.v len) init))
      frame
      (locks_invariant Set.empty m);
    assert (interp
      (pts_to_array a full_permission (Seq.Base.create (U32.v len) init) `star`
      frame `star` locks_invariant Set.empty m) h1
    );
    assert(mem_evolves m m1)
  ) (fun frame m f_frame ->
   let h = heap_of_mem m in
    let a : array_ref t = {
      array_addr = m.ctr;
      array_max_length = len;
      array_length = len;
      array_offset = 0ul;
    } in
    ac_reasoning_for_m_frame_preserving emp frame (locks_invariant Set.empty m) m;
    let (| a, m1 |) = alloc_array_pre_m_action len init m in
    assert (m1.ctr = m.ctr + 1);
    assert (m1.locks == m.locks);
    let h1 = heap_of_mem m1 in
    let single_h = singleton_heap len init a in
    assert (h1 == join single_h h);
    assert(depends_only_on_without_affinity f_frame frame);
    assert (interp ((emp `star` frame) `star` (locks_invariant Set.empty m)) h);
    affine_star (emp `star` frame) (locks_invariant Set.empty m) h;
    affine_star emp frame h;
    assert(interp frame h);
    assert(f_frame h <==> f_frame (join single_h h))
  )
#pop-options

let alloc_array
  (#t: _)
  (len:U32.t)
  (init: t)
  : m_action
    emp
    (a:array_ref t{length a = len /\ offset a = 0ul /\ max_length a = len})
    (fun a -> pts_to_array a full_permission (Seq.Base.create (U32.v len) init))
  =
  alloc_array_is_m_frame_and_preorder_preserving len init;
  alloc_array_pre_m_action len init

let free_array_pre_action
  (#t: _)
  (a: array_ref t{freeable a})
  : pre_action
    (array_perm a full_permission)
    unit
    (fun _ -> emp)
  = fun h -> (| (), h |)

let free_array_action
  (#t: _)
  (a: array_ref t{freeable a})
  =
  pre_action_to_action
    (array_perm a full_permission)
    unit
    (fun _ -> emp)
    (free_array_pre_action a)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 post -> ())
    (fun frame h0 h1  -> ())

let free_array
  (#t: _)
  (a: array_ref t{freeable a})
  : m_action
    (array_perm a full_permission)
    unit
    (fun _ -> emp)
  =
  non_alloc_action_to_non_locking_m_action
    (array_perm a full_permission)
    unit
    (fun _ -> emp)
    (free_array_action a)
    (fun h addr -> ())

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 40"
let share_array_pre_action
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (perm: permission{allows_read perm})
  : pre_action
    (pts_to_array a perm iseq)
    (a':array_ref t{
      length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
      address a = address a'
    })
    (fun a' -> star
      (pts_to_array a (half_permission perm) iseq)
      (pts_to_array a' (half_permission perm) (Ghost.hide (Ghost.reveal iseq)))
    )
    = fun h ->
      let split_h_1 : heap = on _ (fun addr ->
        if addr <> a.array_addr then h addr else
        match h a.array_addr with
        | Some (Array t len seq) ->
          let new_seq = Seq.init len (fun i ->
            if i < U32.v a.array_offset || i >= U32.v a.array_offset + U32.v a.array_length then
              Seq.index seq i
            else match Seq.index seq i with
            | None -> None
            | Some x ->
              assert(perm `lesser_equal_permission` x.perm);
              let new_p = sub_permissions x.perm (half_permission perm) in
              Some ({x with perm = (new_p <: (perm:permission{allows_read perm}))})
          ) in
          assert(Seq.length new_seq = len);
          Some (Array t len new_seq)
        | _ -> h addr
      ) in
      let split_h_2 : heap = on _ (fun addr ->
        if addr <> a.array_addr then None else
        match h a.array_addr with
        | Some (Array t len seq) ->
          let new_seq = Seq.init len (fun i ->
            if i < U32.v a.array_offset || i >= U32.v a.array_offset + U32.v a.array_length then
              None
            else match Seq.index seq i with
            | None -> None
            | Some x ->
              Some ({x with perm = (half_permission perm <: (perm:permission{allows_read perm}))})
          ) in
          assert(Seq.length new_seq = len);
          Some (Array t len new_seq)
        | _ -> None
      ) in
      let aux (addr: addr) : Lemma (h addr == (join split_h_1 split_h_2) addr) =
        if addr <> a.array_addr then () else
        match h addr, (join split_h_1 split_h_2) addr with
        | Some (Array _ _ seq), Some (Array _ _ joint_seq) ->
           assert(seq `Seq.equal` joint_seq)
        | _ -> ()
      in
      Classical.forall_intro aux;
      mem_equiv_eq h (join split_h_1 split_h_2);
      assert(h == join split_h_1 split_h_2);
      (| a, h |)
#pop-options

let share_array_action
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (perm: permission{allows_read perm})
  : action
    (pts_to_array a perm iseq)
    (a':array_ref t{
      length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
      address a = address a'
    })
    (fun a' -> star
      (pts_to_array a (half_permission perm) iseq)
      (pts_to_array a' (half_permission perm) (Ghost.hide (Ghost.reveal iseq)))
    )
  =
  pre_action_to_action
    (pts_to_array a perm iseq)
    (a':array_ref t{
      length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
      address a = address a'
    })
    (fun a' -> star
      (pts_to_array a (half_permission perm) iseq)
      (pts_to_array a' (half_permission perm) (Ghost.hide (Ghost.reveal iseq)))
    )
    (share_array_pre_action a iseq perm)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 ->
      let (|x_alone, h0'|) = share_array_pre_action a iseq perm h0 in
      let (|x_joint, h'|) = share_array_pre_action a iseq perm (join h0 h1) in
      assert(x_alone == x_joint)
    )

let share_array
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (perm: permission{allows_read perm})
  : m_action
    (pts_to_array a perm iseq)
    (a':array_ref t{
      length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
      address a = address a'
    })
    (fun a' -> star
      (pts_to_array a (half_permission perm) iseq)
      (pts_to_array a' (half_permission perm) (Ghost.hide (Ghost.reveal iseq)))
    )
    =
    non_alloc_action_to_non_locking_m_action
       (pts_to_array a perm iseq)
    (a':array_ref t{
      length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
      address a = address a'
    })
    (fun a' -> star
      (pts_to_array a (half_permission perm) iseq)
      (pts_to_array a' (half_permission perm) (Ghost.hide (Ghost.reveal iseq)))
    )
    (share_array_action a iseq perm)
    (fun h addr -> ())

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 40"
let gather_array_pre_action
  (#t: _)
  (a: array_ref t)
  (a':array_ref t{
    length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
    address a = address a'
  })
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: permission{allows_read p})
  (p': permission{allows_read p' /\ summable_permissions p p'})
  : pre_action
    (star
      (pts_to_array a p iseq)
      (pts_to_array a' p' (Ghost.hide (Ghost.reveal iseq)))
    )
    unit
    (fun _ -> pts_to_array a (sum_permissions p p') iseq)
  = fun h ->
    (| (), h |)
#pop-options

#push-options "--max_ifuel 1 --initial_ifuel 1"
let gather_array_action
  (#t: _)
  (a: array_ref t)
  (a':array_ref t{
    length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
    address a = address a'
  })
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: permission{allows_read p})
  (p': permission{allows_read p' /\ summable_permissions p p'})
  : action
    (star
      (pts_to_array a p iseq)
      (pts_to_array a' p' (Ghost.hide (Ghost.reveal iseq)))
    )
    unit
    (fun _ -> pts_to_array a (sum_permissions p p') iseq)
  =
  pre_action_to_action
    (star
      (pts_to_array a p iseq)
      (pts_to_array a' p' (Ghost.hide (Ghost.reveal iseq)))
    )
    unit
    (fun _ -> pts_to_array a (sum_permissions p p') iseq)
    (gather_array_pre_action a a' iseq p p')
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 -> ())
#pop-options

let gather_array
  (#t: _)
  (a: array_ref t)
  (a':array_ref t{
    length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
    address a = address a'
  })
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: permission{allows_read p})
  (p': permission{allows_read p' /\ summable_permissions p p'})
  : m_action
    (star
      (pts_to_array a p iseq)
      (pts_to_array a' p' (Ghost.hide (Ghost.reveal iseq)))
    )
    unit
    (fun _ -> pts_to_array a (sum_permissions p p') iseq)
    =
    non_alloc_action_to_non_locking_m_action
      (star
        (pts_to_array a p iseq)
        (pts_to_array a' p' (Ghost.hide (Ghost.reveal iseq)))
      )
      unit
      (fun _ -> pts_to_array a (sum_permissions p p') iseq)
      (gather_array_action a a' iseq p p')
      (fun h addr -> ())

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 150"
let split_array_pre_action
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: permission{allows_read p})
  (i:U32.t{U32.v i < U32.v (length a)})
  : pre_action
    (pts_to_array a p iseq)
    (as:(array_ref t & array_ref t){(
      length (fst as) = i /\ length (snd as) = U32.sub (length a) i /\
      offset (fst as) = offset a /\ offset (snd as) = U32.add (offset a) i /\
      max_length (fst as) = max_length a /\ max_length (snd as) = max_length a /\
      address (fst as) = address a /\ address (snd as) = address a
    )})
    (fun (a1, a2) -> star
      (pts_to_array a1 p (Seq.slice iseq 0 (U32.v i)))
      (pts_to_array a2 p (Seq.slice iseq (U32.v i) (U32.v (length a))))
    )
  = fun h ->
  let a1 = { a with
    array_offset = a.array_offset;
    array_length = i;
  } in
  let a2 = { a with
    array_offset = U32.add i a.array_offset;
    array_length = U32.sub a.array_length i;
  } in
  let split_h_1 : heap = on _ (fun addr ->
    if addr <> a.array_addr then h addr else
    match h a.array_addr with
    | Some (Array t len seq) ->
      let new_seq = Seq.init len (fun j ->
        if j < U32.v a.array_offset || j >= U32.v a.array_offset + U32.v a.array_length then
          Seq.index seq j
        else if j <  U32.v a.array_offset + U32.v i then
          Seq.index seq j
        else None
      ) in
      assert(Seq.length new_seq = len);
      Some (Array t len new_seq)
    | _ -> h addr
  ) in
   let split_h_2 : heap = on _ (fun addr ->
    if addr <> a.array_addr then None else
    match h a.array_addr with
    | Some (Array t len seq) ->
      let new_seq = Seq.init len (fun j ->
        if j < U32.v a.array_offset || j >= U32.v a.array_offset + U32.v a.array_length then
          None
        else if j <  U32.v a.array_offset + U32.v i then
          None
        else Seq.index seq j
      ) in
      assert(Seq.length new_seq = len);
      Some (Array t len new_seq)
    | _ -> h addr
  ) in
  let aux (addr: addr) : Lemma (h addr == (join split_h_1 split_h_2) addr) =
    if addr <> a.array_addr then () else
    match h addr, (join split_h_1 split_h_2) addr with
    | Some (Array _ _ seq), Some (Array _ _ joint_seq) ->
      assert(seq `Seq.equal` joint_seq)
    | _ -> ()
  in
  Classical.forall_intro aux;
  mem_equiv_eq h (join split_h_1 split_h_2);
  assert(h == join split_h_1 split_h_2);
  (| (a1, a2), h  |)
#pop-options

#push-options "--initial_ifuel 1 --max_ifuel 1"
let split_array_action
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: permission{allows_read p})
  (i:U32.t{U32.v i < U32.v (length a)})
  : action
    (pts_to_array a p iseq)
    (as:(array_ref t & array_ref t){(
      length (fst as) = i /\ length (snd as) = U32.sub (length a) i /\
      offset (fst as) = offset a /\ offset (snd as) = U32.add (offset a) i /\
      max_length (fst as) = max_length a /\ max_length (snd as) = max_length a /\
      address (fst as) = address a /\ address (snd as) = address a
    )})
    (fun (a1, a2) -> star
      (pts_to_array a1 p (Seq.slice iseq 0 (U32.v i)))
      (pts_to_array a2 p (Seq.slice iseq (U32.v i) (U32.v (length a))))
    )
  =
  pre_action_to_action
    (pts_to_array a p iseq)
    (as:(array_ref t & array_ref t){(
      length (fst as) = i /\ length (snd as) = U32.sub (length a) i /\
      offset (fst as) = offset a /\ offset (snd as) = U32.add (offset a) i /\
      max_length (fst as) = max_length a /\ max_length (snd as) = max_length a /\
      address (fst as) = address a /\ address (snd as) = address a
    )})
    (fun (a1, a2) -> star
      (pts_to_array a1 p (Seq.slice iseq 0 (U32.v i)))
      (pts_to_array a2 p (Seq.slice iseq (U32.v i) (U32.v (length a))))
    )
    (split_array_pre_action a iseq p i)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 -> ())
#pop-options

let split_array
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: permission{allows_read p})
  (i:U32.t{U32.v i < U32.v (length a)})
  : m_action
    (pts_to_array a p iseq)
    (as:(array_ref t & array_ref t){(
      length (fst as) = i /\ length (snd as) = U32.sub (length a) i /\
      offset (fst as) = offset a /\ offset (snd as) = U32.add (offset a) i /\
      max_length (fst as) = max_length a /\ max_length (snd as) = max_length a /\
      address (fst as) = address a /\ address (snd as) = address a
    )})
    (fun (a1, a2) -> star
      (pts_to_array a1 p (Seq.slice iseq 0 (U32.v i)))
      (pts_to_array a2 p (Seq.slice iseq (U32.v i) (U32.v (length a))))
    )
  =
  non_alloc_action_to_non_locking_m_action
    (pts_to_array a p iseq)
    (as:(array_ref t & array_ref t){(
      length (fst as) = i /\ length (snd as) = U32.sub (length a) i /\
      offset (fst as) = offset a /\ offset (snd as) = U32.add (offset a) i /\
      max_length (fst as) = max_length a /\ max_length (snd as) = max_length a /\
      address (fst as) = address a /\ address (snd as) = address a
    )})
    (fun (a1, a2) -> star
      (pts_to_array a1 p (Seq.slice iseq 0 (U32.v i)))
      (pts_to_array a2 p (Seq.slice iseq (U32.v i) (U32.v (length a))))
    )
    (split_array_action a iseq p i)
    (fun h addr -> ())


#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 30"
let glue_array_pre_action
  (#t: _)
  (a: array_ref t)
  (a': array_ref t{
    address a = address a' /\ max_length a = max_length a' /\
    offset a' = U32.add (offset a) (length a)
  })
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (iseq': Ghost.erased (Seq.lseq t (U32.v (length a'))))
  (p: permission{allows_read p})
  : pre_action
    (star (pts_to_array a p iseq) (pts_to_array a' p iseq'))
    (new_a:array_ref t{
      address new_a = address a /\ max_length new_a = max_length a /\
      offset new_a = offset a /\ length new_a = U32.add (length a) (length a')
    })
    (fun new_a -> pts_to_array new_a p (Seq.Base.append iseq iseq'))
  = fun h ->
  let new_a : array_ref t = { a with array_length = U32.add a.array_length a'.array_length} in
  (| new_a, h |)
#pop-options

#push-options "--initial_ifuel 1 --max_ifuel 1"
let glue_array_action
  (#t: _)
  (a: array_ref t)
  (a': array_ref t{
    address a = address a' /\ max_length a = max_length a' /\
    offset a' = U32.add (offset a) (length a)
  })
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (iseq': Ghost.erased (Seq.lseq t (U32.v (length a'))))
  (p: permission{allows_read p})
  : action
    (star (pts_to_array a p iseq) (pts_to_array a' p iseq'))
    (new_a:array_ref t{
      address new_a = address a /\ max_length new_a = max_length a /\
      offset new_a = offset a /\ length new_a = U32.add (length a) (length a')
    })
    (fun new_a -> pts_to_array new_a p (Seq.Base.append iseq iseq'))
  =
  pre_action_to_action
    (star (pts_to_array a p iseq) (pts_to_array a' p iseq'))
    (new_a:array_ref t{
      address new_a = address a /\ max_length new_a = max_length a /\
      offset new_a = offset a /\ length new_a = U32.add (length a) (length a')
    })
    (fun new_a -> pts_to_array new_a p (Seq.Base.append iseq iseq'))
    (glue_array_pre_action a a' iseq iseq' p)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 -> ())
#pop-options

let glue_array
  (#t: _)
  (a: array_ref t)
  (a': array_ref t{
    address a = address a' /\ max_length a = max_length a' /\
    offset a' = U32.add (offset a) (length a)
  })
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (iseq': Ghost.erased (Seq.lseq t (U32.v (length a'))))
  (p: permission{allows_read p})
  : m_action
    (star (pts_to_array a p iseq) (pts_to_array a' p iseq'))
    (new_a:array_ref t{
      address new_a = address a /\ max_length new_a = max_length a /\
      offset new_a = offset a /\ length new_a = U32.add (length a) (length a')
    })
    (fun new_a -> pts_to_array new_a p (Seq.Base.append iseq iseq'))
  =
  non_alloc_action_to_non_locking_m_action
    (star (pts_to_array a p iseq) (pts_to_array a' p iseq'))
    (new_a:array_ref t{
      address new_a = address a /\ max_length new_a = max_length a /\
      offset new_a = offset a /\ length new_a = U32.add (length a) (length a')
    })
    (fun new_a -> pts_to_array new_a p (Seq.Base.append iseq iseq'))
    (glue_array_action a a' iseq iseq' p)
    (fun h addr -> ())

///////////////////////////////////////////////////////////////////////////////
// Utilities
///////////////////////////////////////////////////////////////////////////////

let rewrite_hprop_pre (p:hprop) (p':hprop{p `equiv` p'})
  : pre_action p unit (fun _ -> p')
  = fun h -> (| (), h |)

#push-options "--z3rlimit 15 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let rewrite_hprop_action (p:hprop) (p':hprop{p `equiv` p'})
  : action p unit (fun _ -> p') =
  pre_action_to_action
    p
    (x:unit)
    (fun _ -> p')
    (rewrite_hprop_pre p p')
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 -> ())
#pop-options

let rewrite_hprop p p' =
  non_alloc_action_to_non_locking_m_action
    p
    (x:unit)
    (fun _ -> p')
    (rewrite_hprop_action p p')
    (fun h0 addr -> ())

///////////////////////////////////////////////////////////////////////////////
// References
///////////////////////////////////////////////////////////////////////////////

#push-options "--max_fuel 2 --initial_fuel 2"
let sel_ref (#t: Type0) (r: reference t) (h: hheap (ref r)) : t =
  Seq.index (as_seq r h) 0
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2"
let sel_ref_lemma
  (t: Type0)
  (p: permission{allows_read p})
  (r: reference t)
  (m: hheap (ref_perm r p))
  : Lemma (interp (ref r) m /\ interp (pts_to_ref r p (sel_ref r m)) m)
  =
  ()
#pop-options

let get_ref_pre_action
  (#t: Type0)
  (r: reference t)
  (p: permission{allows_read p})
  : pre_action
    (ref_perm r p)
    (x:t)
    (fun x -> pts_to_ref r p x)
  = fun h ->
  let contents = sel_ref r h in
  sel_ref_lemma t p r h;
  let (| x, h' |) = index_array_pre_action r (Seq.create 1 contents) 0ul p h in
  (| x, h' |)


#push-options "--z3rlimit 50 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let get_ref_action
  (#t: Type0)
  (r: reference t)
  (p: permission{allows_read p})
  : action
    (ref_perm r p)
    (x:t)
    (fun x -> pts_to_ref r p x)
  =
  pre_action_to_action
    (ref_perm r p)
    (x:t)
    (fun x -> pts_to_ref r p x)
    (get_ref_pre_action r p)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1  -> ())
#pop-options

let get_ref
  (#t: Type0)
  (r: reference t)
  (p: permission{allows_read p})
  : m_action
    (ref_perm r p)
    (x:t)
    (fun x -> pts_to_ref r p x)
  =
  non_alloc_action_to_non_locking_m_action
    (ref_perm r p)
    (x:t)
    (fun x -> pts_to_ref r p x)
    (get_ref_action r p)
    (fun h0 addr -> ())

let set_ref_pre_action
  (#t: Type0)
  (r: reference t)
  (v: t)
  : pre_action
    (ref_perm r full_permission)
    unit
    (fun _ -> pts_to_ref r full_permission v)
  = fun h ->
  let contents = sel_ref r h in
  sel_ref_lemma t full_permission r h;
  assert(Seq.upd (Seq.create 1 contents) 0 v `Seq.equal` Seq.create 1 v);
  upd_array_pre_action r (Seq.create 1 contents) 0ul v h

let set_ref_action
  (#t: Type0)
  (r: reference t)
  (v: t)
  : action
    (ref_perm r full_permission)
    unit
    (fun _ -> pts_to_ref r full_permission v)
  =
  pre_action_to_action
    (ref_perm r full_permission)
    unit
    (fun _ -> pts_to_ref r full_permission v)
    (set_ref_pre_action r v)
     (fun frame h0 h1 addr -> (* Disjointness preservation *)
     let iseq = Seq.create 1 (sel_ref r h0) in
     sel_ref_lemma t full_permission r h0;
      upd_array_heap_frame_disjointness_preservation r iseq 0ul v (join h0 h1) h0 h1 frame
    )
    (fun frame h0 h1 addr -> (* Does not depend on framing *)
      let iseq = Seq.create 1 (sel_ref r h0) in
      sel_ref_lemma t full_permission r h0;
      upd_array_action_memory_split_independence r iseq 0ul v (join h0 h1) h0 h1 frame
    )
    (fun frame h0 h1  -> (* Return and post *)
      let iseq = Seq.create 1 (sel_ref r h0) in
      sel_ref_lemma t full_permission r h0;
      let (| x0, h |) = set_ref_pre_action r v h0 in
      let (| x1, h' |) = set_ref_pre_action r v (join h0 h1) in
      assert (x0 == x1)
    )

let set_ref
  (#t: Type0)
  (r: reference t)
  (v: t)
  : m_action
    (ref_perm r full_permission)
    unit
    (fun _ -> pts_to_ref r full_permission v)
  =
  non_alloc_action_to_non_locking_m_action
    (ref_perm r full_permission)
    unit
    (fun _ -> pts_to_ref r full_permission v)
    (set_ref_action r v)
    (fun h0 addr -> ())

let alloc_ref
  (#t: Type0)
  (v: t)
  : m_action
    emp
    (reference t)
    (fun r -> pts_to_ref r full_permission v)
  =
  alloc_array 1ul v

let free_ref_pre_action
  (#t: Type0)
  (r: reference t)
  : pre_action
    (ref_perm r full_permission)
    unit
    (fun _ -> emp)
  = fun h ->
    free_array_pre_action r h

let free_ref_action
  (#t: Type0)
  (r: reference t)
  : pre_action
    (ref_perm r full_permission)
    unit
    (fun _ -> emp)
  =
  pre_action_to_action
    (ref_perm r full_permission)
    unit
    (fun _ -> emp)
    (free_ref_pre_action r)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 -> ())


#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 20"
let free_ref
  (#t: Type0)
  (r: reference t)
  : m_action
    (ref_perm r full_permission)
    unit
    (fun _ -> emp)
  =
  non_alloc_action_to_non_locking_m_action
    (ref_perm r full_permission)
    unit
    (fun _ -> emp)
    (free_ref_action r)
    (fun h0 addr -> ())
#pop-options

let share_ref
  (#t: Type0)
  (r: reference t)
  (p: permission{allows_read p})
  (contents: Ghost.erased t)
  : m_action
    (pts_to_ref r p contents)
    (r':reference t{ref_address r' = ref_address r})
    (fun r' ->
      pts_to_ref r (half_permission p) contents `star`
      pts_to_ref r' (half_permission p) contents
    )
  =
  share_array r (Seq.create 1 (Ghost.reveal contents)) p

let gather_ref
  (#t: Type0)
  (r: reference t)
  (r':reference t{ref_address r' = ref_address r})
  (p: permission{allows_read p})
  (p': permission{allows_read p' /\ summable_permissions p p'})
  (contents: Ghost.erased t)
  : m_action
    (pts_to_ref r p contents `star`
      pts_to_ref r' p' contents)
    unit
    (fun _ -> pts_to_ref r (sum_permissions p p') contents)
  =
  gather_array r r' (Seq.create 1 (Ghost.reveal contents)) p p'


////////////////////////////////////////////////////////////////////////////////
// Locks
////////////////////////////////////////////////////////////////////////////////


let lock (p:hprop) = nat

let new_lock_pre_m_action (p:hprop)
  : pre_m_action p (lock p) (fun _ -> emp)
  = fun m ->
     let l = Available p in
     let locks' = l :: m.locks in
     assert (interp (lock_store_invariant Set.empty locks') (heap_of_mem m));
     let mem :mem = { m with locks = locks' } in
     assert (locks_invariant Set.empty mem == p `star` locks_invariant Set.empty m);
     assert (interp (locks_invariant Set.empty mem) (heap_of_mem mem));
     emp_unit (locks_invariant Set.empty mem);
     star_commutative emp (locks_invariant Set.empty mem);
     assert (interp (emp `star` locks_invariant Set.empty mem) (heap_of_mem mem));
     let lock_id = List.Tot.length locks' - 1 in
     (| lock_id, mem |)

let emp_unit_left (p:hprop)
  : Lemma
    ((emp `star` p) `equiv` p)
  = emp_unit p;
    star_commutative emp p

let equiv_star_left (p q r:hprop)
  : Lemma
    (requires q `equiv` r)
    (ensures (p `star` q) `equiv` (p `star` r))
  = ()

#push-options "--warn_error -271 --max_fuel 2 --initial_fuel 2 --admit_smt_queries true"
let new_lock_is_frame_preserving (p:hprop)
  : Lemma (is_m_frame_and_preorder_preserving (new_lock_pre_m_action p))
  = let aux (frame:hprop) (m:hmem (p `star` frame))
      : Lemma
          (ensures (
            let (| x, m1 |) = new_lock_pre_m_action p m in
            interp (emp `star` frame `star` locks_invariant Set.empty m1) (heap_of_mem m1)))
          [SMTPat ()]
      = let (| x, m1 |) = new_lock_pre_m_action p m in
        assert (m1.locks == Available p :: m.locks);
        assert (locks_invariant Set.empty m1 == (p `star` locks_invariant Set.empty m));
        assert (interp ((p `star` frame) `star` locks_invariant Set.empty m) (heap_of_mem m));
        star_associative p frame (locks_invariant Set.empty m);
        assert (interp (p `star` (frame `star` locks_invariant Set.empty m)) (heap_of_mem m));
        star_commutative frame (locks_invariant Set.empty m);
        equiv_star_left p (frame `star` locks_invariant Set.empty m) (locks_invariant Set.empty m `star` frame);
        assert (interp (p `star` (locks_invariant Set.empty m `star` frame)) (heap_of_mem m));
        star_associative p (locks_invariant Set.empty m) frame;
        assert (interp ((p `star` locks_invariant Set.empty m) `star` frame) (heap_of_mem m));
        assert (interp ((locks_invariant Set.empty m1) `star` frame) (heap_of_mem m));
        assert (heap_of_mem m == heap_of_mem m1);
        star_commutative (locks_invariant Set.empty m1) frame;
        assert (interp (frame `star` (locks_invariant Set.empty m1)) (heap_of_mem m1));
        emp_unit_left (frame `star` (locks_invariant Set.empty m1));
        assert (interp (emp `star` (frame `star` (locks_invariant Set.empty m1))) (heap_of_mem m1));
        star_associative emp frame (locks_invariant Set.empty m1)
    in
    ()
#pop-options

let new_lock (p:hprop)
  : m_action p (lock p) (fun _ -> emp)
  = new_lock_is_frame_preserving p;
    new_lock_pre_m_action p

////////////////////////////////////////////////////////////////////////////////
assume
val lock_store_invariant_append (l1 l2:lock_store)
  : Lemma (lock_store_invariant Set.empty (l1 @ l2) `equiv`
           (lock_store_invariant Set.empty l1 `star` lock_store_invariant Set.empty l2))

let lock_ok (#p:hprop) (l:lock p) (m:mem) =
  l < L.length m.locks /\
  (Available? (lock_i m.locks l) \/ Locked? (lock_i m.locks l)) /\
  hprop_of_lock_state (lock_i m.locks l) == p

let lock_ok_stable (#p:_) (l:lock p) (m0 m1:mem)
  : Lemma (lock_ok l m0 /\
           m0 `mem_evolves` m1 ==>
           lock_ok l m1)
  = ()


#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let intro_pure (p:prop) (q:hprop) (h:hheap q { p })
  : hheap (pure p `star` q)
  = emp_unit q;
    star_commutative q emp;
    h
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let intro_hmem_or (p:prop) (q:hprop) (h:hmem q)
  : hmem (h_or (pure p) q)
  = h
#pop-options

let middle_to_head (p q r:hprop) (h:hheap (p `star` (q `star` r)))
  : hheap (q `star` (p `star` r))
  = star_associative p q r;
    star_commutative p q;
    star_associative q p r;
    h

#push-options "--z3rlimit 15 --max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let maybe_acquire #p (l:lock p) (m:hmem emp { lock_ok l m } )
  : (b:bool &
     m:hmem (h_or (pure (b == false)) p))
  = let (| prefix, li, suffix |) = get_lock m.locks l in
    match li with
    | Available _ ->
      let h = heap_of_mem m in
      affine_star emp (lock_store_invariant Set.empty m.locks) h;
      assert (interp (lock_store_invariant Set.empty m.locks) h);
      lock_store_invariant_append prefix (li::suffix);
      assert (lock_store_invariant Set.empty m.locks `equiv`
             (lock_store_invariant Set.empty prefix `star`
                      (p `star` lock_store_invariant Set.empty suffix)));
      assert (interp (lock_store_invariant Set.empty prefix `star`
                       (p `star` lock_store_invariant Set.empty suffix)) h);
      let h = middle_to_head (lock_store_invariant Set.empty prefix) p (lock_store_invariant Set.empty suffix) h in
      assert (interp (p `star`
                        (lock_store_invariant Set.empty prefix `star`
                         lock_store_invariant Set.empty suffix)) h);
      let new_lock_store = prefix @ (Locked p :: suffix) in
      lock_store_invariant_append prefix (Locked p :: suffix);
      assert (lock_store_invariant Set.empty new_lock_store `equiv`
              (lock_store_invariant Set.empty prefix `star`
                         lock_store_invariant Set.empty suffix));
      equiv_star_left p (lock_store_invariant Set.empty new_lock_store)
                        (lock_store_invariant Set.empty prefix `star`
                          lock_store_invariant Set.empty suffix);
      assert (interp (p `star` lock_store_invariant Set.empty new_lock_store) h);
      let h : hheap (p `star` lock_store_invariant Set.empty new_lock_store) = h in
      assert (heap_of_mem m == h);
      star_commutative p (lock_store_invariant Set.empty new_lock_store);
      affine_star (lock_store_invariant Set.empty new_lock_store) p h;
      assert (interp (lock_store_invariant Set.empty new_lock_store) h);
      let mem : hmem p = { m with locks = new_lock_store } in
      let b = true in
      let mem : hmem (h_or (pure (b==false)) p) = intro_hmem_or (b == false) p mem in
      (| b, mem |)

    | Locked _ ->
      let b = false in
      assert (interp (pure (b == false)) (heap_of_mem m));
      affine_star emp (lock_store_invariant Set.empty m.locks) (heap_of_mem m);
      let h : hheap (locks_invariant Set.empty m) = heap_of_mem m in
      let h : hheap (pure (b==false) `star` locks_invariant Set.empty m) =
        intro_pure (b==false) (locks_invariant Set.empty m) h in
      intro_or_l (pure (b==false) `star` locks_invariant Set.empty m)
                 (p `star` locks_invariant Set.empty m)
                 h;
      or_star (pure (b==false)) p (locks_invariant Set.empty m) h;
      assert (interp (h_or (pure (b==false)) p `star` locks_invariant Set.empty m) h);
      (| false, m |)
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let hmem_emp (p:hprop) (m:hmem p) : hmem emp = m
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 60"
let release #p (l:lock p) (m:hmem p { lock_ok l m } )
  : (b:bool &
     hmem emp)
  = let (| prefix, li, suffix |) = get_lock m.locks l in
    let h = heap_of_mem m in
    lock_store_invariant_append prefix (li::suffix);
    assert (interp (p `star`
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
      assert (interp (p `star`
                        (lock_store_invariant Set.empty prefix `star`
                          (lock_store_invariant Set.empty suffix))) h);
      let h = middle_to_head p (lock_store_invariant Set.empty prefix) (lock_store_invariant Set.empty suffix) h in
      assert (interp (lock_store_invariant Set.empty prefix `star`
                        (p `star`
                          (lock_store_invariant Set.empty suffix))) h);
      let new_lock_store = prefix @ (Available p :: suffix) in
      lock_store_invariant_append prefix (Available p :: suffix);
      assert (lock_store_invariant Set.empty new_lock_store `equiv`
                (lock_store_invariant Set.empty prefix `star`
                 (p `star` lock_store_invariant Set.empty (suffix))));
      assert (interp (lock_store_invariant Set.empty new_lock_store) h);
      emp_unit_left (lock_store_invariant Set.empty new_lock_store);
      let mem : hmem emp = { m with locks = new_lock_store } in
      (| true, mem |)
#pop-options

///////////////////////////////////////////////////////////////////////////////
// Invariants
///////////////////////////////////////////////////////////////////////////////

let inv (p:hprop) = nat

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
     assert (interp (lock_store_invariant Set.empty locks') (heap_of_mem m));
     let mem :mem = { m with locks = locks' } in
     assert (locks_invariant Set.empty mem == p `star` locks_invariant Set.empty m);
     assert (interp (locks_invariant Set.empty mem) (heap_of_mem mem));
     emp_unit (locks_invariant Set.empty mem);
     star_commutative emp (locks_invariant Set.empty mem);
     assert (interp (emp `star` locks_invariant Set.empty mem) (heap_of_mem mem));
     let lock_id = List.Tot.length locks' - 1 in
     (| lock_id, mem |)

#push-options "--warn_error -271 --max_fuel 2 --initial_fuel 2 --admit_smt_queries true"
let new_inv_is_frame_preserving (p:hprop)
  : Lemma (is_m_frame_and_preorder_preserving (new_inv_pre_m_action p))
  = let aux (frame:hprop) (m:hmem (p `star` frame))
      : Lemma
          (ensures (
            let (| x, m1 |) = new_inv_pre_m_action p m in
            interp (emp `star` frame `star` locks_invariant Set.empty m1) (heap_of_mem m1)))
          [SMTPat ()]
      = let (| x, m1 |) = new_inv_pre_m_action p m in
        assert (m1.locks == Invariant p :: m.locks);
        assert (locks_invariant Set.empty m1 == (p `star` locks_invariant Set.empty m));
        assert (interp ((p `star` frame) `star` locks_invariant Set.empty m) (heap_of_mem m));
        star_associative p frame (locks_invariant Set.empty m);
        assert (interp (p `star` (frame `star` locks_invariant Set.empty m)) (heap_of_mem m));
        star_commutative frame (locks_invariant Set.empty m);
        equiv_star_left p (frame `star` locks_invariant Set.empty m) (locks_invariant Set.empty m `star` frame);
        assert (interp (p `star` (locks_invariant Set.empty m `star` frame)) (heap_of_mem m));
        star_associative p (locks_invariant Set.empty m) frame;
        assert (interp ((p `star` locks_invariant Set.empty m) `star` frame) (heap_of_mem m));
        assert (interp ((locks_invariant Set.empty m1) `star` frame) (heap_of_mem m));
        assert (heap_of_mem m == heap_of_mem m1);
        star_commutative (locks_invariant Set.empty m1) frame;
        assert (interp (frame `star` (locks_invariant Set.empty m1)) (heap_of_mem m1));
        emp_unit_left (frame `star` (locks_invariant Set.empty m1));
        assert (interp (emp `star` (frame `star` (locks_invariant Set.empty m1))) (heap_of_mem m1));
        star_associative emp frame (locks_invariant Set.empty m1)
    in
    ()
#pop-options

let new_inv (p:hprop)
  : m_action p (inv p) (fun _ -> emp)
  = new_inv_is_frame_preserving p;
    new_inv_pre_m_action p

let pre_atomic (uses:Set.set lock_addr)
               (fp:hprop)
               (a:Type)
               (fp':a -> hprop) =
    m:hmem' uses fp -> (x:a & hmem' uses (fp' x))

let is_atomic_frame_and_preorder_preserving
  (#uses:Set.set lock_addr) (#a:Type) (#fp:hprop) (#fp':a -> hprop)
  (f:pre_atomic uses fp a fp') =
  forall (frame:hprop) (m0:hmem' uses (fp `star` frame)).
    (ac_reasoning_for_m_frame_preserving fp frame (locks_invariant uses m0) m0;
     let (| x, m1 |) = f m0 in
     interp ((fp' x `star` frame) `star` locks_invariant uses m1) (heap_of_mem m1) /\
     mem_evolves m0 m1 /\
     (forall (f_frame:fp_prop frame). f_frame (heap_of_mem m0) <==> f_frame (heap_of_mem m1)))

let atomic (uses:Set.set lock_addr)
           (fp:hprop)
           (a:Type)
           (fp':a -> hprop) =
    f:pre_atomic uses fp a fp'{ is_atomic_frame_and_preorder_preserving f}

let promote_action_preatomic
    (#a:Type) (#fp:hprop) (#fp':a -> hprop)
    (uses:Set.set lock_addr)
    (f:action fp a fp')
    (non_alloc: (h: hheap fp) -> (addr: addr) -> Lemma
      (requires (h addr == None))
      (ensures (let (| _, h'|) = f h in h' addr == None))
    )

   : pre_atomic uses fp a fp' =
   fun (m0:hmem' uses fp) ->

       let h0 = heap_of_mem m0 in
       let (| x, h1 |) = f h0 in
       Classical.forall_intro (Classical.move_requires (non_alloc h0));
       let m1 = { m0 with heap = h1 } in
       (| x, m1 |)

val action_to_atomic_frame_aux
    (uses:Set.set lock_addr)
    (#fp:hprop) (#a:Type) (#fp':a -> hprop)
    (f:action fp a fp')
    (non_alloc: (h: hheap fp) -> (addr: addr) -> Lemma
      (requires (h addr == None))
      (ensures (let (| _, h'|) = f h in h' addr == None))
    )
    (frame:hprop) (m0:hmem' uses (fp `star` frame))
    : Lemma (
        ac_reasoning_for_m_frame_preserving fp frame (locks_invariant uses m0) m0;
        interp (fp `star` locks_invariant uses m0) (heap_of_mem m0) /\
        (let (| x, m1 |) = (promote_action_preatomic uses f non_alloc) m0 in
        interp ((fp' x `star` frame) `star` locks_invariant uses m1) (heap_of_mem m1) /\
        mem_evolves m0 m1 /\
        (forall (f_frame:fp_prop frame). f_frame (heap_of_mem m0) <==> f_frame (heap_of_mem m1))))

let action_to_atomic_frame_aux uses #fp #a #fp' f non_alloc frame m0 =
  ac_reasoning_for_m_frame_preserving fp frame (locks_invariant uses m0) m0;
  let h0 = heap_of_mem m0 in
  let (| x, h1 |) = f h0 in
  Classical.forall_intro (Classical.move_requires (non_alloc h0));
  let m1 = { m0 with heap = h1 } in

  star_associative fp frame (locks_invariant uses m0);
  star_associative (fp' x) frame (locks_invariant uses m1)

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
    (f:action fp a fp')
    (non_alloc: (h: hheap fp) -> (addr: addr) -> Lemma
      (requires (h addr == None))
      (ensures (let (| _, h'|) = f h in h' addr == None))
    )
    : atomic uses fp a fp' =
    action_to_atomic_frame uses f non_alloc;
    promote_action_preatomic uses f non_alloc

val atomic_satisfies_mem_evolves
  (#a:Type) (#fp:hprop) (#fp':a -> hprop) (#uses:Set.set lock_addr)
  (f:atomic uses fp a fp')
  (m0:hmem' uses fp)
  : Lemma (let (| _, m1 |) = f m0 in mem_evolves m0 m1)

let atomic_satisfies_mem_evolves #a #fp #fp' #uses f m0 =
  calc (equiv) {
    fp `star` locks_invariant uses m0;
    (equiv) { emp_unit fp;
              star_congruence fp (locks_invariant uses m0) (fp `star` emp) (locks_invariant uses m0)}
    (fp `star` emp) `star` locks_invariant uses m0;
  };
  let m0:hmem' uses (fp `star` emp) = m0 in
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
    locks_invariant uses m0 `equiv`
    (p `star` locks_invariant (Set.union (Set.singleton i) uses) m0))
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
    (frame `star` locks_invariant uses m0) `equiv`
    ((p `star` frame) `star` locks_invariant (Set.union (Set.singleton i) uses) m0))
  = let istore' = locks_invariant (Set.union (Set.singleton i) uses) m0 in
    calc (equiv) {
         frame `star` locks_invariant uses m0;
         (equiv) { interp_inv_not_in_uses' i uses m0;
                   star_congruence frame (locks_invariant uses m0) frame
                     (p `star` istore') }
         frame `star` (p `star` istore');
         (equiv) { star_associative frame p istore';
                   star_commutative frame p;
                   star_congruence (frame `star` p) istore' (p `star` frame) istore'}
         (p `star` frame) `star` istore';
    }



val pre_with_invariant
  (#a:Type) (#fp:hprop) (#fp':a -> hprop) (#uses:Set.set lock_addr)
  (#p:hprop)
  (i:inv p{not (i `Set.mem` uses)})
  (f:atomic (Set.union (Set.singleton i) uses) (p `star` fp) a (fun x -> p `star` fp' x))
  : pre_atomic uses fp a fp'

let pre_with_invariant #a #fp #fp' #uses #p i f =
  fun (m0:hmem' uses fp) ->
    assume (inv_ok i m0);
    let uses' = Set.union (Set.singleton i) uses in
    interp_inv_not_in_uses i uses fp m0;
    let (| x, m1 |) = f m0 in
    atomic_satisfies_mem_evolves f m0;
    interp_inv_not_in_uses i uses (fp' x) m1;
    (| x, m1 |)

val with_invariant_frame_aux
    (#fp:hprop) (#a:Type) (#fp':a -> hprop) (#uses:Set.set lock_addr)
    (#p:hprop)
    (i:inv p{not (i `Set.mem` uses)})
    (f:atomic (Set.union (Set.singleton i) uses) (p `star` fp) a (fun x -> p `star` fp' x))
    (frame:hprop) (m0:hmem' uses (fp `star` frame))
    : Lemma (
        ac_reasoning_for_m_frame_preserving fp frame (locks_invariant uses m0) m0;
        interp (fp `star` locks_invariant uses m0) (heap_of_mem m0) /\
        (let (| x, m1 |) = (pre_with_invariant i f) m0 in
        interp ((fp' x `star` frame) `star` locks_invariant uses m1) (heap_of_mem m1) /\
        mem_evolves m0 m1 /\
        (forall (f_frame:fp_prop frame). f_frame (heap_of_mem m0) <==> f_frame (heap_of_mem m1))))

#push-options "--fuel 0 --ifuel 0"
let with_invariant_frame_aux #fp #a #fp' #uses #p i f frame m0 =
  assume (inv_ok i m0);
  ac_reasoning_for_m_frame_preserving fp frame (locks_invariant uses m0) m0;
  let uses' = Set.union (Set.singleton i) uses in
  calc (equiv) {
    ((fp `star` frame) `star` locks_invariant uses m0);
    (equiv) { interp_inv_not_in_uses i uses (fp `star` frame) m0 }
    (p `star` (fp `star` frame)) `star` locks_invariant uses' m0;
    (equiv) { star_associative p fp frame;
              star_congruence ((p `star` fp) `star` frame) (locks_invariant uses' m0)
                              (p `star` (fp `star` frame)) (locks_invariant uses' m0)}
    ((p `star` fp) `star` frame) `star` locks_invariant uses' m0;
  };
  calc (equiv) {
    fp `star` locks_invariant uses m0;
    (equiv) { interp_inv_not_in_uses i uses fp m0 }
    (p `star` fp) `star` locks_invariant uses' m0;
  };
  let m0:hmem' uses' ((p `star` fp) `star` frame) = m0 in
  let (| x, m1 |) = f m0 in
  atomic_satisfies_mem_evolves f m0;
  calc (equiv) {
    ((p `star` fp' x) `star` frame) `star` locks_invariant uses' m1;
    (equiv) { star_associative p (fp' x) frame;
              star_congruence ((p `star` fp' x) `star` frame) (locks_invariant uses' m1)
                              (p `star` (fp' x `star` frame)) (locks_invariant uses' m1)}
    (p `star` (fp' x `star` frame)) `star` locks_invariant uses' m1;
    (equiv) { interp_inv_not_in_uses i uses (fp' x `star` frame) m1 }
    (fp' x `star` frame) `star` locks_invariant uses m1;
  }
#pop-options

val with_invariant_frame
    (#fp:hprop) (#a:Type) (#fp':a -> hprop) (#uses:Set.set lock_addr)
    (#p:hprop)
    (i:inv p{not (i `Set.mem` uses)})
    (f:atomic (Set.union (Set.singleton i) uses) (p `star` fp) a (fun x -> p `star` fp' x))
    :  Lemma (is_atomic_frame_and_preorder_preserving (pre_with_invariant i f))

let with_invariant_frame #fp #a #fp' #uses #p i f =
  Classical.forall_intro_2 (with_invariant_frame_aux i f)

val with_invariant
  (#a:Type) (#fp:hprop) (#fp':a -> hprop) (#uses:Set.set lock_addr)
  (#p:hprop)
  (i:inv p{not (i `Set.mem` uses)})
  (f:atomic (Set.union (Set.singleton i) uses) (p `star` fp) a (fun x -> p `star` fp' x))
  : atomic uses fp a fp'

let with_invariant #a #fp #fp' #uses #p i f =
    with_invariant_frame i f;
    pre_with_invariant i f
