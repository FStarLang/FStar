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
module Steel.Actions.Pointer
open Steel.Heap
open Steel.HProp
open FStar.Real
open Steel.Permissions
module U32 = FStar.UInt32
open Steel.Actions
open FStar.FunctionalExtensionality

friend Steel.Heap
friend Steel.HProp
friend Steel.Memory
friend Steel.Actions

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"


////////////////////////////////////////////////////////////////////////////////
// sel
////////////////////////////////////////////////////////////////////////////////
#push-options "--max_fuel 3"
let sel #a (r:ref a) (m:hheap (ptr r))
  : a
  = let Ref _ _ v = select_addr m r in
    v
#pop-options

#push-options "--max_fuel 2"
let sel_lemma #a (r:ref a) (p:permission) (m:hheap (ptr_perm r p))
  = ()
#pop-options


let upd_heap #a (r:ref a) (v:a)
  : pre_action (ptr_perm r full_permission) unit (fun _ -> pts_to r full_permission v)
  = fun h -> (| (), update_addr h r (Ref a full_permission v) |)

#push-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 10"
let upd_lemma' (#a:_) (r:ref a) (v:a) (h:heap) (frame:hprop)
  : Lemma
    (requires
      interp (ptr_perm r full_permission `star` frame) h)
    (ensures (
      let (| x, h1 |) = upd_heap r v h in
      interp (pts_to r full_permission v `star` frame) h1))
  = let aux (h0 h1:heap)
     : Lemma
       (requires
         disjoint h0 h1 /\
         h == join h0 h1 /\
         interp (ptr_perm r full_permission) h0 /\
         interp frame h1)
       (ensures (
         let (| _, h' |) = upd_heap r v h in
         let h0' = update_addr h0 r (Ref a full_permission v) in
         disjoint h0' h1 /\
         interp (pts_to r full_permission v) h0' /\
         interp frame h1 /\
         h' == join h0' h1))
       [SMTPat (disjoint h0 h1)]
     = let (| _, h'|) = upd_heap r v h in
       let h0' = update_addr h0 r (Ref a full_permission v) in
       assume (disjoint h0' h1);  //AR: 12/11: TODO
       mem_equiv_eq h' (join h0' h1)
   in
   ()
#pop-options


#push-options "--warn_error -271"
let upd'_is_frame_preserving (#a:_) (r:ref a) (v:a)
  : Lemma (is_frame_preserving (upd_heap r v))
  = let aux (#a:_) (r:ref a) (v:a) (h:heap) (frame:hprop)
      : Lemma
        (requires
          interp (ptr_perm r full_permission `star` frame) h)
        (ensures (
          let (| _, h1 |) = (upd_heap r v h) in
          interp (pts_to r full_permission v `star` frame) h1))
        [SMTPat ()]
      = upd_lemma' r v h frame
   in
   ()
#pop-options

#push-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let upd'_preserves_join #a (r:ref a) (v:a)
                       (h0:hheap (ptr_perm r full_permission))
                       (h1:heap {disjoint h0 h1})
  : Lemma
     (let (| x0, h |) = upd_heap r v h0 in
      let (| x1, h' |) = upd_heap r v (join h0 h1) in
      x0 == x1 /\
      disjoint h h1 /\
      h' == join h h1)
  = let (| x0, h |) = upd_heap r v h0 in
    let (| x1, h' |) = upd_heap r v (join h0 h1) in
    assert (h == update_addr h0 r (Ref a full_permission v));
    assert (h' == update_addr (join h0 h1) r (Ref a full_permission v));
    assert (disjoint h h1);
    assert (h' `mem_equiv` join h h1)
#pop-options

#push-options "--warn_error -271"
let upd'_depends_only_on_fp #a (r:ref a) (v:a)
  : Lemma (action_depends_only_on_fp (upd_heap r v))
  =
    let pre = ptr_perm r full_permission in
    let post = pts_to r full_permission v in
    let aux (h0:hheap pre)
            (h1:heap {disjoint h0 h1})
            (q:fp_prop post)
    : Lemma
      (let (| x0, h |) = upd_heap r v h0 in
        let (| x1, h' |) = upd_heap r v (join h0 h1) in
        x0 == x1 /\
        (q h <==> q h'))
      [SMTPat ()]
    = let (| x0, h |) = upd_heap r v h0 in
      let (| x1, h' |) = upd_heap r v (join h0 h1) in
      assert (x0 == x1);
      upd'_preserves_join r v h0 h1;
      assert (h' == join h h1)
    in
    ()
#pop-options

#push-options "--z3rlimit 50 --max_fuel 2 --initial_fuel 2"
let upd' #a (r:ref a) (v:a)
  : pre_m_action (ptr_perm r full_permission) unit (fun _ -> pts_to r full_permission v)
  = fun m ->
      upd'_is_frame_preserving r v;
      let (| _, h' |) = upd_heap r v m.heap in
      let m':mem = {m with heap = h'} in
      (| (), m' |)
#pop-options

#push-options "--warn_error -271 --initial_fuel 2 --max_fuel 2"
let upd_is_frame_preserving (#a:_) (r:ref a) (v:a)
  : Lemma (is_m_frame_preserving (upd' r v))
  =
  let aux (#a:_) (r:ref a) (v:a) (frame:hprop) (m:hmem (ptr_perm r full_permission `star` frame))
      : Lemma
        (ensures (
          let (| _, m1 |) = upd' r v m in
          interp (pts_to r full_permission v `star` frame `star` locks_invariant m1) m1.heap))
        [SMTPat ()]
      = star_associative (ptr_perm r full_permission) frame (locks_invariant m);
        star_associative (pts_to r full_permission v) frame (locks_invariant m);
        upd_lemma' r v m.heap (frame `star` locks_invariant m)
   in
   ()
#pop-options

#push-options "--warn_error -271"
let upd_depends_only_on_fp (#a:_) (r:ref a) (v:a)
  : Lemma (m_action_depends_only_on (upd' r v))
  =
    let pre = ptr_perm r full_permission in
    let post = pts_to r full_permission v in
    let aux (m0:hmem pre)
            (h1:heap {m_disjoint m0 h1})
            (q:fp_prop post)
    : Lemma
      (let (| x0, m |) = upd' r v m0 in
       let (| x1, m' |) = upd' r v (upd_joined_heap m0 h1) in
        x0 == x1 /\
        (q (heap_of_mem m) <==> q (heap_of_mem m')))
      [SMTPat ()]
    = let (| x0, m |) = upd' r v m0 in
      let (| x1, m' |) = upd' r v (upd_joined_heap m0 h1) in
      upd'_preserves_join r v m0.heap h1;
      assert (m'.heap == join m.heap h1)
    in
    ()
#pop-options

let upd #a (r:ref a) (v:a)
  : m_action (ptr_perm r full_permission) unit (fun _ -> pts_to r full_permission v)
  = upd_is_frame_preserving r v;
    upd_depends_only_on_fp r v;
    upd' r v

val alloc' (#a:_) (v:a) (frame:hprop) (tmem:mem{interp frame (heap_of_mem tmem)})
  : (x:ref a &
     tmem:mem { interp (pts_to x full_permission v `star` frame) (heap_of_mem tmem)} )


#push-options "--max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let alloc' #a v frame m
  = let x : ref a = m.ctr in
    let cell = Ref a full_permission v in
    let mem : heap = on _ (fun i -> if i = x then Some cell else None) in
    assert (disjoint mem m.heap);
    assert (mem `contains_addr` x);
    assert (select_addr mem x == cell);
    let mem' = join mem m.heap in
    intro_pts_to x full_permission v mem;
    assert (interp (pts_to x full_permission v) mem);
    assert (interp frame m.heap);
    intro_star (pts_to x full_permission v) frame mem m.heap;
    assert (interp (pts_to x full_permission v `star` frame) mem');
    let t = {
      ctr = x + 1;
      heap = mem';
      locks = m.locks;
      properties = ();
    } in
    (| x, t |)
#pop-options

let singleton_heap #a (x:ref a) (c:cell) : heap =
    on _ (fun i -> if i = x then Some c else None)

let singleton_pts_to #a (x:ref a) (c:cell{Ref? c})
  : Lemma (requires (Ref?.a c == a))
          (ensures (interp (pts_to x (Ref?.perm c) (Ref?.v c)) (singleton_heap x c)))
  = ()

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 50"
let alloc_pre_m_action (#a:_) (v:a)
  : pre_m_action emp (ref a) (fun x -> pts_to x full_permission v)
  = fun m ->
    let x : ref a = m.ctr in
    let cell = Ref a full_permission v in
    let mem : heap = singleton_heap x cell in
    assert (disjoint mem m.heap);
    assert (mem `contains_addr` x);
    assert (select_addr mem x == cell);
    let mem' = join mem m.heap in
    intro_pts_to x full_permission v mem;
    assert (interp (pts_to x full_permission v) mem);
    let frame = (lock_store_invariant m.locks) in
    assert (interp frame m.heap);
    intro_star (pts_to x full_permission v) frame mem m.heap;
    assert (interp (pts_to x full_permission v `star` frame) mem');
    let t = {
      ctr = x + 1;
      heap = mem';
      locks = m.locks;
      properties = ();
    } in
    (| x, t |)
#pop-options

#push-options "--z3rlimit 70 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let alloc_is_frame_preserving' (#a:_) (v:a) (m:mem) (frame:hprop)
  : Lemma
    (requires
      interp (frame `star` locks_invariant m) (heap_of_mem m))
    (ensures (
      let (| x, m1 |) = alloc_pre_m_action v m in
      interp (pts_to x full_permission v `star` frame `star` locks_invariant m1) (heap_of_mem m1)))
  = let (| x, m1 |) = alloc_pre_m_action v m in
    assert (x == m.ctr);
    assert (m1.ctr = m.ctr + 1);
    assert (m1.locks == m.locks);
    let h = heap_of_mem m in
    let h1 = heap_of_mem m1 in
    let cell = (Ref a full_permission v) in
    assert (h1 == join (singleton_heap x cell) h);
    intro_pts_to x full_permission v (singleton_heap x cell);
    singleton_pts_to x cell;
    assert (interp (pts_to x full_permission v) (singleton_heap x cell));
    assert (interp (frame `star` locks_invariant m) h);
    intro_star (pts_to x full_permission v) (frame `star` locks_invariant m) (singleton_heap x cell) h;
    assert (interp (pts_to x full_permission v `star` (frame `star` locks_invariant m)) h1);
    star_associative (pts_to x full_permission v) frame (locks_invariant m);
    assert (interp (pts_to x full_permission v `star` frame `star` locks_invariant m) h1)
#pop-options

#push-options "--z3rlimit 150 --warn_error -271 --initial_fuel 2 --max_fuel 2"
let alloc_is_frame_preserving (#a:_) (v:a)
  : Lemma (is_m_frame_preserving (alloc_pre_m_action v))
  = let aux (frame:hprop) (m:hmem (emp `star` frame))
      : Lemma
          (ensures (
            let (| x, m1 |) = alloc_pre_m_action v m in
            interp (pts_to x full_permission v `star` frame `star` locks_invariant m1) (heap_of_mem m1)))
          [SMTPat ()]
      = alloc_is_frame_preserving' v m frame
    in
    ()
#pop-options

#push-options "--z3rlimit 10 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let alloc_preserves_disjoint (#a:_) (v:a) (m0:hmem emp) (h1:heap {m_disjoint m0 h1})
  : Lemma (let (| x0, m |) = alloc_pre_m_action v m0 in
           disjoint (heap_of_mem m) h1)
  = let (| x0, m |) = alloc_pre_m_action v m0 in
    let h0 = heap_of_mem m0 in
    let h' = heap_of_mem m in
    let aux (ad:addr) : Lemma (disjoint_addr h' h1 ad)
      = if ad >= m0.ctr then ()
        else begin
          let h_alloc = singleton_heap #a m0.ctr (Ref a full_permission v) in
          assert (h' == join h_alloc h0);
          assert (h_alloc ad == None);
         assert (h0 ad == h' ad);
         assert (disjoint_addr h0 h1 ad)
        end
    in Classical.forall_intro aux
#pop-options

#push-options "--z3rlimit 30 --max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let alloc_preserves_join (#a:_) (v:a) (m0:hmem emp) (h1:heap {m_disjoint m0 h1})
  : Lemma (
      let h0 = heap_of_mem m0 in
      let h = join h0 h1 in
      let m1:mem = { m0 with heap = h } in
      let (| x0, m |) = (alloc_pre_m_action v) m0 in
      let (| x1, m' |) = (alloc_pre_m_action v) m1 in
      heap_of_mem m' == join (heap_of_mem m) h1)
   = let h0 = heap_of_mem m0 in
     let h = join h0 h1 in
     let m1:mem = { m0 with heap = h } in
     let (| x0, m |) = (alloc_pre_m_action v) m0 in
     let (| x1, m' |) = (alloc_pre_m_action v) m1 in
     let h_alloc = singleton_heap #a m0.ctr (Ref a full_permission v) in
     // let hm = heap_of_mem m in
     // let hm' = heap_of_mem m' in
     // assert (hm == join h_alloc h0);
     // assert (hm' == join h_alloc h);
     // assert (hm' == join h_alloc (join h0 h1));
     join_associative' h_alloc h0 h1
#pop-options

#push-options "--z3rlimit 10 --warn_error -271"
let alloc_depends_only_on (#a:_) (v:a)
  : Lemma (m_action_depends_only_on (alloc_pre_m_action v))
  = let aux
        (m0:hmem emp)
        (h1:heap { m_disjoint m0 h1 })
        (post:(x:ref a -> fp_prop (pts_to x full_permission v)))
      : Lemma
          (ensures (
            let h0 = heap_of_mem m0 in
            let h = join h0 h1 in
            let m1 = { m0 with heap = h } in
            let (| x0, m |) = (alloc_pre_m_action v) m0 in
            let (| x1, m' |) = (alloc_pre_m_action v) m1 in
            x0 == x1 /\
            (post x0 (heap_of_mem m) <==> post x1 (heap_of_mem m'))))
          [SMTPat ()]
      =
        let h0 = heap_of_mem m0 in
        let h = join h0 h1 in
        let m1 = { m0 with heap = h } in
        let (| x0, m |) = (alloc_pre_m_action v) m0 in
        let (| x1, m' |) = (alloc_pre_m_action v) m1 in
        assert (x0 == x1);
        alloc_preserves_disjoint v m0 h1;
//        assert (disjoint (heap_of_mem m) h1);
        affine_star (pts_to x0 full_permission v) (locks_invariant m) (heap_of_mem m);
        alloc_preserves_join v m0 h1
//        assert (interp (pts_to x0 full_permission v) (heap_of_mem m));
//        assert (heap_of_mem m' == join (heap_of_mem m) h1)
    in
    ()
#pop-options

let alloc (#a:_) (v:a)
  : m_action emp (ref a) (fun x -> pts_to x full_permission v)
  = alloc_is_frame_preserving v;
    alloc_depends_only_on v;
    alloc_pre_m_action v
