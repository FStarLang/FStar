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

let m_action_depends_only_on #pre #a #post (f:pre_m_action pre a post)
  = forall (m0:hmem pre)
      (h1:heap {m_disjoint m0 h1})
      (post: (x:a -> fp_prop (post x))).
      (let m1 = upd_joined_heap m0 h1 in
       let (| x0, m |) = f m0 in
       let (| x1, m' |) = f m1 in
       x0 == x1 /\
       (post x0 (heap_of_mem m) <==> post x1 (heap_of_mem m')))

#push-options "--initial_fuel 2 --max_fuel 2"
let is_m_frame_preserving #a #fp #fp' (f:pre_m_action fp a fp') =
  forall frame (m0:hmem (fp `star` frame)).
    (affine_star fp frame (heap_of_mem m0);
     let (| x, m1 |) = f m0 in
     interp (fp' x `star` frame `star` locks_invariant m1) (heap_of_mem m1))
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --z3rlimit 10"
let frame_fp_prop' #fp #a #fp' frame
                   (q:fp_prop frame)
                   (act:action fp a fp')
                   (h0:hheap (fp `star` frame))
   : Lemma (requires q h0)
           (ensures (
             let (| x, h1 |) = act h0 in
             q h1))
   = assert (interp (Refine (fp `star` frame) q) h0);
     assert (interp (fp `star` (Refine frame q)) h0);
     let (| x, h1 |) = act h0 in
     assert (interp (fp' x `star` (Refine frame q)) h1);
     refine_star_r (fp' x) frame q;
     assert (interp (Refine (fp' x `star` frame) q) h1);
     assert (q h1)
#pop-options

let frame_fp_prop #fp #a #fp' (act:action fp a fp')
                  (#frame:hprop) (q:fp_prop frame)
   = let aux (h0:hheap (fp `star` frame))
       : Lemma
         (requires q h0)
         (ensures
           (let (|x, h1|) = act h0 in
            q h1))
         [SMTPat (act h0)]
       = frame_fp_prop' frame q act h0
     in
     ()


////////////////////////////////////////////////////////////////////////////////
// References
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

#push-options "--z3rlimit 10 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let upd_disjointness_lemma'
  #a (r:ref a) (v:a)
  (h0 h1:heap)
  (frame:hprop)
  : Lemma
    (requires
      disjoint h0 h1 /\
      interp (ptr_perm r full_permission) h0 /\
      interp frame h1)
    (ensures (
      let h0' = update_addr h0 r (Ref a full_permission v) in
      disjoint h0' h1))
  =
  let aux (addr: addr) : Lemma (
    let h0' = update_addr h0 r (Ref a full_permission v) in
    disjoint_addr h0' h1 addr
  ) =
    let h0' = update_addr h0 r (Ref a full_permission v) in
    match h0' addr, h1 addr, h0 addr with
    | Some (Ref a0' p0' x0'), Some (Ref a1 p1 x1),
      Some (Ref a0 p0 x0) ->
      if addr = r then begin
        assert(Permission?.r p0 +. Permission?.r p1 <=. 1.0R);
        assert(full_permission `lesser_equal_permission` p0);
        assert(Permission?.r p1 = 0.0R);
        assert(Permission?.r p1 >. 0.0R)
      end else begin
        ()
      end
    | _ -> ()
  in
  Classical.forall_intro aux
#pop-options

#push-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 30"
let upd_lemma' (#a:_) (r:ref a) (v:a) (h:heap) (frame:hprop)
  : Lemma
    (requires
      interp (ptr_perm r full_permission `star` frame) h)
    (ensures (
      let (| x, h1 |) = upd_heap r v h in
      interp (pts_to r full_permission v `star` frame) h1 /\
      preserves_frame_prop frame h h1))
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
       upd_disjointness_lemma' r v h0 h1 frame;
       assert (disjoint h0' h1);
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
          interp (pts_to r full_permission v `star` frame) h1 /\
          preserves_frame_prop frame h h1))
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

#push-options "--z3rlimit 50 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let alloc_preserves_frame_prop  (#a:_) (v:a) (m:mem) (frame:hprop)
  : Lemma (requires
      interp (frame `star` locks_invariant m) (heap_of_mem m))
          (ensures  (
      let (| x, m1 |) = alloc_pre_m_action v m in
      preserves_frame_prop frame (heap_of_mem m) (heap_of_mem m1)))
      = ()
#pop-options

#push-options "--z3rlimit 150 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let alloc_is_frame_preserving' (#a:_) (v:a) (m:mem) (frame:hprop)
  : Lemma
    (requires
      interp (frame `star` locks_invariant m) (heap_of_mem m))
    (ensures (
      let (| x, m1 |) = alloc_pre_m_action v m in
      interp (pts_to x full_permission v `star` frame `star` locks_invariant m1) (heap_of_mem m1) /\
      preserves_frame_prop frame (heap_of_mem m) (heap_of_mem m1)))
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
    assert (interp (pts_to x full_permission v `star` frame `star` locks_invariant m) h1);
    alloc_preserves_frame_prop v m frame
#pop-options

#push-options "--z3rlimit 150 --warn_error -271 --initial_fuel 2 --max_fuel 2"
let alloc_is_frame_preserving (#a:_) (v:a)
  : Lemma (is_m_frame_preserving (alloc_pre_m_action v))
  = let aux (frame:hprop) (m:hmem (emp `star` frame))
      : Lemma
          (ensures (
            let (| x, m1 |) = alloc_pre_m_action v m in
            interp (pts_to x full_permission v `star` frame `star` locks_invariant m1) (heap_of_mem m1) /\
            preserves_frame_prop frame (heap_of_mem m) (heap_of_mem m1)))
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

/////////////////////////////////////////////////////////////////////////////
// Arrays
/////////////////////////////////////////////////////////////////////////////

#push-options "--max_fuel 3"
let as_seq (#t:_) (a:array_ref t) (m:hheap (array a)) =
  let Array t' len' seq = select_addr m a.array_addr in
  let len = U32.v a.array_length in
  assert(U32.v a.array_offset + U32.v a.array_length <= len');
  Seq.init len (fun i -> let (x, _) =  select_index seq (U32.v a.array_offset + i) in x)
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

let index
  (#t:_)
  (a:array_ref t)
  (iseq: Seq.lseq t (U32.v (length a)))
  (p: permission)
  (i:U32.t{U32.v i < U32.v (length a)}) =
  magic() //TODO: DM 12/18/2019

let update_addr_array
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
        let new_seq = Seq.upd seq (U32.v i + U32.v a.array_offset) (Some (v, perm)) in
        Some (Array t len new_seq)
      else
        m a'
    )
   | _ -> m

#push-options "--max_fuel 2 --initial_fuel 2"
let upd_array_seq'
  (#t:_)
  (a:array_ref t)
  (iseq: Seq.lseq t (U32.v (length a)))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (h: hheap (pts_to_array a full_permission iseq)) : heap =
  let Array _ len v_orig = select_addr h a.array_addr in
  update_addr_array a i v full_permission h
#pop-options

let upd_array_heap
  (#t:_)
  (a:array_ref t)
  (iseq: Seq.lseq t (U32.v (length a)))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  : pre_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> pts_to_array a full_permission (Seq.upd iseq (U32.v i) v))
  = fun h ->
    (| (), upd_array_seq' a iseq i v h |)

#push-options "--z3rlimit 15 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let upd_array_disjointness_lemma'
  (#t:_)
  (a:array_ref t)
  (iseq: Seq.lseq t (U32.v (length a)))
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
      let h0' = upd_array_seq' a iseq i v h0 in
      disjoint h0' h1))
  =
  ()
#pop-options

#push-options "--z3rlimit 30 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let upd_array_joint_lemma'
  (#t:_)
  (a:array_ref t)
  (iseq: Seq.lseq t (U32.v (length a)))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (h h0 h1:heap)
  (frame:hprop)
  (addr: addr)
  : Lemma
    (requires
      disjoint h0 h1 /\
      h == join h0 h1 /\
      interp (pts_to_array a full_permission iseq) h0 /\
      interp frame h1)
    (ensures (
      let (| _, h' |) = upd_array_heap a iseq i v h in
      let h0' = upd_array_seq' a iseq i v h0 in
      upd_array_disjointness_lemma' a iseq i v h h0 h1 frame;
      h' addr == (join h0' h1) addr))
  =
  let (| _, h' |) = upd_array_heap a iseq i v h in
  let h0' = upd_array_seq' a iseq i v h0 in
  upd_array_disjointness_lemma' a iseq i v h h0 h1 frame;
  if addr <> a.array_addr then () else
  if not (h1 `contains_addr` addr) then ()
  else match  h' addr, (join h0' h1) addr with
  | Some (Array t2 len2 seq2), Some (Array t3 len3 seq3) ->
    assert(seq2 `Seq.equal` seq3)
  | _ -> ()
#pop-options

#push-options "--z3rlimit 150 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let upd_array_lemma'
  (#t:_)
  (a:array_ref t)
  (iseq: Seq.lseq t (U32.v (length a)))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (h:heap)
  (frame:hprop)
  : Lemma
    (requires
      interp (pts_to_array a full_permission iseq `star` frame) h)
    (ensures (
      let (| _, h1 |) = upd_array_heap a iseq i v h in
      interp (pts_to_array a full_permission (Seq.upd iseq (U32.v i) v)  `star` frame) h1 /\
      preserves_frame_prop frame h h1))
  = let aux (h0 h1:heap)
     : Lemma
       (requires
         disjoint h0 h1 /\
         h == join h0 h1 /\
         interp (pts_to_array a full_permission iseq) h0 /\
         interp frame h1)
       (ensures (
         let (| _, h' |) = upd_array_heap a iseq i v h in
         let h0' = upd_array_seq' a iseq i v h0 in
         disjoint h0' h1 /\
         interp (pts_to_array a full_permission (Seq.upd iseq (U32.v i) v)) h0' /\
         interp frame h1 /\
         h' == join h0' h1))
       [SMTPat (disjoint h0 h1)]
     =
     let (| _, h'|) = upd_array_heap a iseq i v h in
     let h0' = upd_array_seq' a iseq i v h0 in
     upd_array_disjointness_lemma' a iseq i v h h0 h1 frame;
     let aux (addr: addr) : Lemma (h' addr == (join h0' h1) addr) =
       upd_array_joint_lemma' a iseq i v h h0 h1 frame addr
     in
     Classical.forall_intro aux;
     mem_equiv_eq h' (join h0' h1)
   in
   ()
#pop-options

#push-options "--warn_error -271"
let upd_array'_is_frame_preserving
  (#t:_)
  (a:array_ref t)
  (iseq: Seq.lseq t (U32.v (length a)))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  : Lemma (is_frame_preserving (upd_array_heap a iseq i v))
  = let aux
    (#t:_)
    (a:array_ref t)
    (iseq: Seq.lseq t (U32.v (length a)))
    (i:U32.t{U32.v i < U32.v (length a)})
    (v: t) (h:heap) (frame:hprop)
      : Lemma
        (requires
          interp (pts_to_array a full_permission iseq `star` frame) h)
        (ensures (
          let (| _, h1 |) = (upd_array_heap a iseq i v h) in
          interp (pts_to_array a full_permission (Seq.upd iseq (U32.v i) v) `star` frame) h1 /\
          preserves_frame_prop frame h h1))
        [SMTPat ()]
      = upd_array_lemma' a iseq i v h frame
   in
   ()
#pop-options

#push-options "--z3rlimit 10 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let upd_array_disjointness_lemma2'
  (#t:_)
  (a:array_ref t)
  (iseq: Seq.lseq t (U32.v (length a)))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (h0:hheap (pts_to_array a full_permission iseq))
  (h1:heap {disjoint h0 h1})
  : Lemma
    (requires True)
    (ensures (
      let (| _, h |) = upd_array_heap a iseq i v h0 in
      disjoint h h1))
  = ()
#pop-options

#push-options "--z3rlimit 30 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let upd_array'_preserves_join
  (#t:_)
  (a:array_ref t)
  (iseq: Seq.lseq t (U32.v (length a)))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (h0:hheap (pts_to_array a full_permission iseq))
  (h1:heap {disjoint h0 h1})
  : Lemma
     (let (| x0, h |) = upd_array_heap a iseq i v h0 in
      let (| x1, h' |) = upd_array_heap a iseq i v (join h0 h1) in
      x0 == x1 /\
      disjoint h h1 /\
      h' == join h h1)
  =
    let (| x0, h |) = upd_array_heap a iseq i v h0 in
    let (| x1, h' |) = upd_array_heap a iseq i v (join h0 h1) in
    upd_array_disjointness_lemma2' a iseq i v h0 h1;
    let aux (addr: addr) : Lemma (h' addr == (join h h1) addr) =
       if addr <> a.array_addr then () else
       if not (h1 `contains_addr` addr) then ()
       else match  h' addr, (join h h1) addr with
         | Some (Array t2 len2 seq2), Some (Array t3 len3 seq3) ->
          assert(seq2 `Seq.equal` seq3)
         | _ -> ()
     in
     Classical.forall_intro aux;
    assert (h' `mem_equiv` join h h1)
#pop-options

#push-options "--warn_error -271"
let upd_array'_depends_only_on_fp
  (#t:_)
  (a:array_ref t)
  (iseq: Seq.lseq t (U32.v (length a)))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  : Lemma (action_depends_only_on_fp (upd_array_heap a iseq i v))
  =
    let pre = pts_to_array a full_permission iseq in
    let post = pts_to_array a full_permission (Seq.upd iseq (U32.v i) v) in
    let aux (h0:hheap pre)
            (h1:heap {disjoint h0 h1})
            (q:fp_prop post)
    : Lemma
      (let (| x0, h |) = upd_array_heap a iseq i v h0 in
        let (| x1, h' |) = upd_array_heap a iseq i v (join h0 h1) in
        x0 == x1 /\
        (q h <==> q h'))
      [SMTPat ()]
    = let (| x0, h |) = upd_array_heap a iseq i v h0 in
      let (| x1, h' |) = upd_array_heap a iseq i v (join h0 h1) in
      assert (x0 == x1);
      upd_array'_preserves_join a iseq i v h0 h1;
      assert (h' == join h h1)
    in
    ()
#pop-options

#push-options "--z3rlimit 300 --max_fuel 2 --initial_fuel 2"
let upd_array'
  (#t:_)
  (a:array_ref t)
  (iseq: Seq.lseq t (U32.v (length a)))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  : pre_m_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> pts_to_array a full_permission (Seq.upd iseq (U32.v i) v))
  = fun m ->
      upd_array'_is_frame_preserving a iseq i v;
      upd_array'_depends_only_on_fp a iseq i v;
      let (| _, h' |) = upd_array_heap a iseq i v m.heap in
      let m':mem = {m with heap = h'} in
      (| (), m' |)
#pop-options

#push-options "--warn_error -271 --initial_fuel 2 --max_fuel 2 --z3rlimit 20"
let upd_array_is_frame_preserving
  (#t:_)
  (a:array_ref t)
  (iseq: Seq.lseq t (U32.v (length a)))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  : Lemma (is_m_frame_preserving (upd_array' a iseq i v))
  =
  let aux
    (#t:_)
    (a:array_ref t)
    (iseq: Seq.lseq t (U32.v (length a)))
    (i:U32.t{U32.v i < U32.v (length a)})
    (v: t)
    (frame:hprop) (m:hmem (pts_to_array a full_permission iseq `star` frame))
      : Lemma
        (ensures (
          let (| _, m1 |) = upd_array' a iseq i v m in
          interp (pts_to_array a full_permission (Seq.upd iseq (U32.v i) v) `star` frame `star` locks_invariant m1) m1.heap))
        [SMTPat ()]
      = star_associative (pts_to_array a full_permission iseq) frame (locks_invariant m);
        star_associative (pts_to_array a full_permission (Seq.upd iseq (U32.v i) v)) frame (locks_invariant m);
        upd_array_lemma' a iseq i v m.heap (frame `star` locks_invariant m)
   in
   ()
#pop-options

#push-options "--warn_error -271"
let upd_array_depends_only_on_fp
    (#t:_)
    (a:array_ref t)
    (iseq: Seq.lseq t (U32.v (length a)))
    (i:U32.t{U32.v i < U32.v (length a)})
    (v: t)
  : Lemma (m_action_depends_only_on (upd_array' a iseq i v))
  =
    let pre = pts_to_array a full_permission iseq in
    let post = pts_to_array a full_permission (Seq.upd iseq (U32.v i) v) in
    let aux (m0:hmem pre)
            (h1:heap {m_disjoint m0 h1})
            (q:fp_prop post)
    : Lemma
      (let (| x0, m |) = upd_array' a iseq i v m0 in
       let (| x1, m' |) = upd_array' a iseq i v (upd_joined_heap m0 h1) in
        x0 == x1 /\
        (q (heap_of_mem m) <==> q (heap_of_mem m')))
      [SMTPat ()]
    = let (| x0, m |) = upd_array' a iseq i v m0 in
      let (| x1, m' |) = upd_array' a iseq i v (upd_joined_heap m0 h1) in
      upd_array'_preserves_join a iseq i v m0.heap h1;
      assert (m'.heap == join m.heap h1)
    in
    ()
#pop-options

let upd_array
  (#t:_)
  (a:array_ref t)
  (iseq: Seq.lseq t (U32.v (length a)))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  : m_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> pts_to_array a full_permission (Seq.upd iseq (U32.v i) v))
  = upd_array_is_frame_preserving a iseq i v;
    upd_array_depends_only_on_fp a iseq i v;
    upd_array' a iseq i v

////////////////////////////////////////////////////////////////////////////////
// Locks
////////////////////////////////////////////////////////////////////////////////


let lock (p:hprop) = nat

module L = FStar.List.Tot

let new_lock_pre_m_action (p:hprop)
  : pre_m_action p (lock p) (fun _ -> emp)
  = fun m ->
     let l = Available p in
     let locks' = l :: m.locks in
     assert (interp (lock_store_invariant locks') (heap_of_mem m));
     let mem :mem = { m with locks = locks' } in
     assert (locks_invariant mem == p `star` locks_invariant m);
     assert (interp (locks_invariant mem) (heap_of_mem mem));
     emp_unit (locks_invariant mem);
     star_commutative emp (locks_invariant mem);
     assert (interp (emp `star` locks_invariant mem) (heap_of_mem mem));
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

#push-options "--warn_error -271 --max_fuel 2 --initial_fuel 2"
let new_lock_is_frame_preserving (p:hprop)
  : Lemma (is_m_frame_preserving (new_lock_pre_m_action p))
  = let aux (frame:hprop) (m:hmem (p `star` frame))
      : Lemma
          (ensures (
            let (| x, m1 |) = new_lock_pre_m_action p m in
            interp (emp `star` frame `star` locks_invariant m1) (heap_of_mem m1)))
          [SMTPat ()]
      = let (| x, m1 |) = new_lock_pre_m_action p m in
        assert (m1.locks == Available p :: m.locks);
        assert (locks_invariant m1 == (p `star` locks_invariant m));
        assert (interp ((p `star` frame) `star` locks_invariant m) (heap_of_mem m));
        star_associative p frame (locks_invariant m);
        assert (interp (p `star` (frame `star` locks_invariant m)) (heap_of_mem m));
        star_commutative frame (locks_invariant m);
        equiv_star_left p (frame `star` locks_invariant m) (locks_invariant m `star` frame);
        assert (interp (p `star` (locks_invariant m `star` frame)) (heap_of_mem m));
        star_associative p (locks_invariant m) frame;
        assert (interp ((p `star` locks_invariant m) `star` frame) (heap_of_mem m));
        assert (interp ((locks_invariant m1) `star` frame) (heap_of_mem m));
        assert (heap_of_mem m == heap_of_mem m1);
        star_commutative (locks_invariant m1) frame;
        assert (interp (frame `star` (locks_invariant m1)) (heap_of_mem m1));
        emp_unit_left (frame `star` (locks_invariant m1));
        assert (interp (emp `star` (frame `star` (locks_invariant m1))) (heap_of_mem m1));
        star_associative emp frame (locks_invariant m1)
    in
    ()
#pop-options

let new_lock (p:hprop)
  : m_action p (lock p) (fun _ -> emp)
  = new_lock_is_frame_preserving p;
    new_lock_pre_m_action p

////////////////////////////////////////////////////////////////////////////////
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

assume
val lock_store_invariant_append (l1 l2:lock_store)
  : Lemma (lock_store_invariant (l1 @ l2) `equiv`
           (lock_store_invariant l1 `star` lock_store_invariant l2))

let hprop_of_lock_state (l:lock_state) : hprop =
  match l with
  | Available p -> p
  | Locked p -> p

let lock_ok (#p:hprop) (l:lock p) (m:mem) =
  l < L.length m.locks /\
  hprop_of_lock_state (lock_i m.locks l) == p

let lock_store_evolves : Preorder.preorder lock_store =
  fun (l1 l2 : lock_store) ->
    L.length l2 >= L.length l1 /\
    (forall (i:nat{i < L.length l1}).
       hprop_of_lock_state (lock_i l1 i) ==
       hprop_of_lock_state (lock_i l2 i))

let mem_evolves : Preorder.preorder mem =
  fun m0 m1 -> lock_store_evolves m0.locks m1.locks

let lock_ok_stable (#p:_) (l:lock p) (m0 m1:mem)
  : Lemma (lock_ok l m0 /\
           m0 `mem_evolves` m1 ==>
           lock_ok l m1)
  = ()

let pure (p:prop) : hprop = refine emp (fun _ -> p)

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

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let maybe_acquire #p (l:lock p) (m:mem { lock_ok l m } )
  : (b:bool &
     m:hmem (h_or (pure (b == false)) p))
  = let (| prefix, li, suffix |) = get_lock m.locks l in
    match li with
    | Available _ ->
      let h = heap_of_mem m in
      assert (interp (lock_store_invariant m.locks) h);
      lock_store_invariant_append prefix (li::suffix);
      assert (lock_store_invariant m.locks `equiv`
             (lock_store_invariant prefix `star`
                      (p `star` lock_store_invariant suffix)));
      assert (interp (lock_store_invariant prefix `star`
                       (p `star` lock_store_invariant suffix)) h);
      let h = middle_to_head (lock_store_invariant prefix) p (lock_store_invariant suffix) h in
      assert (interp (p `star`
                        (lock_store_invariant prefix `star`
                         lock_store_invariant suffix)) h);
      let new_lock_store = prefix @ (Locked p :: suffix) in
      lock_store_invariant_append prefix (Locked p :: suffix);
      assert (lock_store_invariant new_lock_store `equiv`
              (lock_store_invariant prefix `star`
                         lock_store_invariant suffix));
      equiv_star_left p (lock_store_invariant new_lock_store)
                        (lock_store_invariant prefix `star`
                          lock_store_invariant suffix);
      assert (interp (p `star` lock_store_invariant new_lock_store) h);
      let h : hheap (p `star` lock_store_invariant new_lock_store) = h in
      assert (heap_of_mem m == h);
      star_commutative p (lock_store_invariant new_lock_store);
      affine_star (lock_store_invariant new_lock_store) p h;
      assert (interp (lock_store_invariant new_lock_store) h);
      let mem : hmem p = { m with locks = new_lock_store } in
      let b = true in
      let mem : hmem (h_or (pure (b==false)) p) = intro_hmem_or (b == false) p mem in
      (| b, mem |)

    | Locked _ ->
      let b = false in
      assert (interp (pure (b == false)) (heap_of_mem m));
      let h : hheap (locks_invariant m) = heap_of_mem m in
      let h : hheap (pure (b==false) `star` locks_invariant m) =
        intro_pure (b==false) (locks_invariant m) h in
      intro_or_l (pure (b==false) `star` locks_invariant m)
                 (p `star` locks_invariant m)
                 h;
      or_star (pure (b==false)) p (locks_invariant m) h;
      assert (interp (h_or (pure (b==false)) p `star` locks_invariant m) h);
      (| false, m |)
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let hmem_emp (p:hprop) (m:hmem p) : hmem emp = m
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 20"
let release #p (l:lock p) (m:hmem p { lock_ok l m } )
  : (b:bool &
     hmem emp)
  = let (| prefix, li, suffix |) = get_lock m.locks l in
    let h = heap_of_mem m in
    lock_store_invariant_append prefix (li::suffix);
    assert (interp (p `star`
                     (lock_store_invariant prefix `star`
                       (lock_store_invariant (li::suffix)))) h);
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
                        (lock_store_invariant prefix `star`
                          (lock_store_invariant suffix))) h);
      let h = middle_to_head p (lock_store_invariant prefix) (lock_store_invariant suffix) h in
      assert (interp (lock_store_invariant prefix `star`
                        (p `star`
                          (lock_store_invariant suffix))) h);
      let new_lock_store = prefix @ (Available p :: suffix) in
      lock_store_invariant_append prefix (Available p :: suffix);
      assert (lock_store_invariant new_lock_store `equiv`
                (lock_store_invariant prefix `star`
                 (p `star` lock_store_invariant (suffix))));
      assert (interp (lock_store_invariant new_lock_store) h);
      emp_unit_left (lock_store_invariant new_lock_store);
      let mem : hmem emp = { m with locks = new_lock_store } in
      (| true, mem |)
#pop-options
