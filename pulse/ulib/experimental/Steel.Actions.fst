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

#push-options "--max_fuel 2 --initial_fuel 2 --z3rlimit 30"
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

#push-options "--warn_error -271"
let action_depends_only_on_fp_intro (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_action fp a fp')
  (lemma:
    (h0:hheap fp) ->
    (h1:heap{disjoint h0 h1}) ->
    (post: (x:a -> fp_prop (fp' x))) ->
    Lemma (interp fp (join h0 h1) /\ (
      let (|x0, h0'|) = f h0 in
      let (|x1, h'|) = f (join h0 h1) in
      x0 == x1 /\
      (post x0 h0' <==> post x1 h')
    ))
  )
  : Lemma (action_depends_only_on_fp f)
  =
  let aux (h0:hheap fp) (h1:heap {disjoint h0 h1}) (post: (x:a -> fp_prop (fp' x)))
    : Lemma (interp fp (join h0 h1) /\ (
      let (| x0, h |) = f h0 in
      let (| x1, h' |) = f (join h0 h1) in
      x0 == x1 /\
      (post x0 h <==> post x1 h')
    ))
   =
     lemma h0 h1 post
   in
   Classical.forall_intro_3 aux;
   admit() //TODO: DM 22/01/20 figure out why F* can't recognize the intro...
#pop-options

#push-options "--z3rlimit 50 --max_ifuel 3 --initial_ifuel 3 --max_fuel 3 --initial_fuel 3"
let action_depends_only_on_fp_elim
  (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_action fp a fp')
  (h0: hheap fp) (h1:heap{disjoint h0 h1}) (post: (x:a -> fp_prop (fp' x)))
  : Lemma (requires (action_depends_only_on_fp f)) (ensures (
    interp fp (join h0 h1) /\ (
     let (| x0, h |) = f h0 in
     let (| x1, h' |) = f (join h0 h1) in
     x0 == x1 /\
     (post x0 h <==> post x1 h'))
  ))
=
  admit() //TODO DM 24/01/20 figure out why F* can't recognize it
#pop-options

#push-options "--max_fuel 2 --initial_ifuel 2"
let is_frame_preserving_intro
  (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_action fp a fp')
  (preserves_frame_prop_intro:
    (frame: hprop) -> (h0: heap) ->
    (q: (heap -> prop){q `depends_only_on_without_affinity` frame}) ->
    Lemma (requires (interp (fp `star` frame) h0)) (ensures (
      let (| x, h1 |) = f h0 in q h0 <==> q h1
    ))
  )
  (preserves_framing_intro:
    (frame: hprop) -> (h0: heap) ->
    Lemma (requires (interp (fp `star` frame) h0)) (ensures (
      let (| x, h1 |) = f h0 in  interp (fp' x `star` frame) h1
    ))
  )
  : Lemma (is_frame_preserving f)
  =
  let aux (frame: hprop) (h0: heap) : Lemma (interp (fp `star` frame) h0 ==>
     (let (| x, h1 |) = f h0 in
     interp (fp' x `star` frame) h1 /\
     preserves_frame_prop frame h0 h1)
  ) =
    let aux (pf: (interp (fp `star` frame) h0)) : Lemma (
      interp (fp `star` frame) h0 /\ (
      let h0 : (h0:heap{interp fp h0}) = affine_star fp frame h0; h0 in
      let (| x, h1 |) = f h0 in
      interp (fp' x `star` frame) h1 /\
      preserves_frame_prop frame h0 h1)
    ) =
      affine_star fp frame h0;
      let (| x, h1 |) = f h0 in
      let aux (q: (heap -> prop){q `depends_only_on_without_affinity` frame})
        : Lemma (q h0 <==> q h1) =
        preserves_frame_prop_intro frame h0 q
      in
      Classical.forall_intro aux;
      assert(preserves_frame_prop frame h0 h1);
      preserves_framing_intro frame h0
    in
    Classical.impl_intro aux
  in
  Classical.forall_intro_2 aux
#pop-options

let is_frame_preserving_elim
  (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_action fp a fp')
  (frame: hprop) (h0: heap)
  : Lemma (requires (is_frame_preserving f /\ interp (fp `star` frame) h0)) (ensures (
     let (| x, h1 |) = f h0 in
     interp (fp' x `star` frame) h1 /\
     preserves_frame_prop frame h0 h1
  ))
  = ()

#push-options "--z3rlimit 100 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
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
  (action_return_and_post_does_not_depend_on_framing:
    (frame: hprop) ->
    (h0:hheap fp) ->
    (h1:hheap frame{disjoint h0 h1}) ->
    (post: (x:a -> fp_prop (fp' x))) ->
    Lemma (
      let (|x_alone, h0'|) = f h0 in
      let (|x_joint, h'|) = f (join h0 h1) in
      x_alone == x_joint /\
      (post x_alone h0' <==> post x_joint h')
    )
  )
  : Tot (action fp a fp')
  =
  let aux (frame: hprop) (h: hheap (fp `star` frame))
    : Lemma (
      let (|x, h' |) = f h in
      preserves_frame_prop frame h h' /\
      interp (fp' x `star` frame) h'
    )
    =
    let (| x, h' |) = f h in
    let pf :squash (exists (h0:heap). (exists (h1:heap).
      disjoint h0 h1 /\ h == join h0 h1 /\ interp fp h0 /\ interp frame h1
    )) =
      assert(interp (fp `star` frame) h)
    in
    Classical.exists_elim
      (preserves_frame_prop frame h h' /\ interp (fp' x `star` frame) h') pf
      (fun h0 ->
        let pf: squash (exists (h1: hheap frame).
          disjoint h0 h1 /\ h == join h0 h1 /\ interp fp h0 /\ interp frame h1
        ) =
          ()
        in
        Classical.exists_elim
          (preserves_frame_prop frame h h' /\ interp (fp' x `star` frame) h') pf
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
            let aux (q:(heap -> prop){q `depends_only_on_without_affinity` frame})
              : Lemma (q h <==> q h')
            = ()
            in
            Classical.forall_intro aux;
            action_return_and_post_does_not_depend_on_framing frame h0 h1 (fun _ _ -> True);
            assert(x_alone == x);
            assert(x_joint == x);
            assert(interp (fp' x_alone) h0');
            assert(interp frame h1);
            assert(h' == join h0' h1);
            assert(disjoint h0' h1);
            intro_star (fp' x) (frame) h0' h1;
            assert(interp (fp' x `star` frame) h')
        )
    )
  in
  Classical.forall_intro_2 aux;
  let aux (h0:hheap fp) (h1:heap {disjoint h0 h1}) (post: (x:a -> fp_prop (fp' x)))
    : Lemma (
       let (| x0, h0' |) = f h0 in
       let (| x1, h' |) = f (join h0 h1) in
       interp fp (join h0 h1) /\
       x0 == x1 /\
       (post x0 h0' <==> post x1 h')
    )
    =
      let (| x0, h0' |) = f h0 in
      let (| x1, h' |) = f (join h0 h1) in
      action_return_and_post_does_not_depend_on_framing emp h0 h1 post
  in
  action_depends_only_on_fp_intro f aux;
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
    assert(interp (lock_store_invariant m.locks) h');
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
    assert(interp (lock_store_invariant m.locks) h');
    let m':mem = {m with heap = h'; ctr = m.ctr + 1} in
    (| x, m' |)
#pop-options

#push-options "--warn_error -271"
let m_action_depends_only_on_intro (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_m_action fp a fp')
  (lemma:
    (m0:hmem fp) ->
    (h1:heap{m_disjoint m0 h1}) ->
    (post: (x:a -> fp_prop (fp' x))) ->
    Lemma (
      let m1 = upd_joined_heap m0 h1 in
      let (|x0, m|) = f m0 in
      let (|x1, m'|) = f m1 in
      x0 == x1 /\
      (post x0 (heap_of_mem m) <==> post x1 (heap_of_mem m'))
    )
  )
  : Lemma (m_action_depends_only_on f)
  =
  let aux (m0:hmem fp) (h1:heap {m_disjoint m0 h1}) (post: (x:a -> fp_prop (fp' x)))
    : Lemma (
     let m1 = upd_joined_heap m0 h1 in
      let (|x0, m|) = f m0 in
      let (|x1, m'|) = f m1 in
      x0 == x1 /\
      (post x0 (heap_of_mem m) <==> post x1 (heap_of_mem m'))
    )
   =
     lemma m0 h1 post
   in
   Classical.forall_intro_3 aux;
   admit() //TODO: DM 22/01/20 figure out why F* can't recognize the intro...
#pop-options

#restart-solver

#push-options "--max_fuel 2 --initial_ifuel 2 --z3rlimit 20"
let is_m_frame_preserving_intro
  (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_m_action fp a fp')
  (preserves_framing_intro:
    (frame: hprop) -> (m0: hmem (fp `star` frame)) ->
    Lemma (
      let (| x, m1 |) = f m0 in
      interp (fp' x `star` frame `star` locks_invariant m1) (heap_of_mem m1)
    )
  )
  : Lemma (is_m_frame_preserving f)
  =
  let aux (frame: hprop) (m0: hmem (fp `star` frame)) : Lemma (
     affine_star fp frame m0.heap;
     let (| x, m1 |) = f m0 in
     interp (fp' x `star` frame `star` locks_invariant m1) (heap_of_mem m1)
  ) =
    let (| x, h1 |) = f m0 in
    preserves_framing_intro frame m0
  in
  Classical.forall_intro_2 aux
#pop-options

#push-options "--z3rlimit 50 --max_ifuel 0 --initial_ifuel 0 --max_fuel 1 --initial_fuel 1"
let non_alloc_action_to_non_locking_m_action
  (fp:hprop) (a: Type) (fp': a -> hprop) (f: action fp a fp')
    (non_alloc: (h: hheap fp) -> (addr: addr) -> Lemma
    (requires (h addr == None))
    (ensures (let (| _, h'|) = f h in h' addr == None))
  )
  : Tot (m_action fp a fp')
=
  let f_m = non_alloc_action_to_non_locking_pre_m_action fp a fp' f non_alloc in
  m_action_depends_only_on_intro f_m (fun m0 h1 post ->
    let m1 = upd_joined_heap m0 h1 in
    let (|x0, m|) = f_m m0 in
    let (|x1, m'|) = f_m m1 in
    assert(action_depends_only_on_fp f);
    action_depends_only_on_fp_elim f m0.heap h1 post;
    assert(x0 == x1);
    assert(post x0 (heap_of_mem m) <==> post x1 (heap_of_mem m'))
  );
  assert(m_action_depends_only_on f_m);
  is_m_frame_preserving_intro f_m (fun frame m0 ->
    star_associative fp frame (locks_invariant m0);
    let (| x, m1 |) = f_m m0 in
    star_associative (fp' x) frame (locks_invariant m1);
    is_frame_preserving_elim f frame m0.heap
  );
  assert(is_m_frame_preserving f_m);
  f_m
#pop-options

#push-options "--z3rlimit 50 --max_ifuel 0 --initial_ifuel 0 --max_fuel 1 --initial_fuel 1"
let alloc_action_to_non_locking_m_action
  (fp:hprop) (a: Type) (fp': a -> hprop) (f: action fp a fp')
  (non_alloc: (h: hheap fp) -> (addr: addr) -> Lemma
    (requires (h addr == None))
    (ensures (let (| _, h'|) = f h in h' addr == None))
  )
  : Tot (m_action fp a fp')
=
  let f_m = non_alloc_action_to_non_locking_pre_m_action fp a fp' f non_alloc in
  m_action_depends_only_on_intro f_m (fun m0 h1 post ->
    let m1 = upd_joined_heap m0 h1 in
    let (|x0, m|) = f_m m0 in
    let (|x1, m'|) = f_m m1 in
    assert(action_depends_only_on_fp f);
    action_depends_only_on_fp_elim f m0.heap h1 post;
    assert(x0 == x1);
    assert(post x0 (heap_of_mem m) <==> post x1 (heap_of_mem m'))
  );
  assert(m_action_depends_only_on f_m);
  is_m_frame_preserving_intro f_m (fun frame m0 ->
    star_associative fp frame (locks_invariant m0);
    let (| x, m1 |) = f_m m0 in
    star_associative (fp' x) frame (locks_invariant m1);
    is_frame_preserving_elim f frame m0.heap
  );
  assert(is_m_frame_preserving f_m);
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
    | Some (x, _) -> x
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
    (fun frame h0 h1 post -> ())

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
        let new_seq = Seq.upd seq (U32.v i + U32.v a.array_offset) (Some (v, perm)) in
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

#push-options "--z3rlimit 100 --max_fuel 1 --initial_fuel 1 --initial_ifuel 1 --max_ifuel 1"
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
    (fun frame h0 h1 post -> (* Return and post *)
      let (| x0, h |) = upd_array_pre_action a iseq i v h0 in
      let (| x1, h' |) = upd_array_pre_action a iseq i v (join h0 h1) in
      assert (x0 == x1);
      upd_array_heap_frame_disjointness_preservation a iseq i v (join h0 h1) h0 h1 frame;
      upd_array_action_memory_split_independence a iseq i v (join h0 h1) h0 h1 frame;
      assert (h' == join h h1)
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
      Some (init, (full_permission <: (perm:permission{allows_read perm})))
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
  assert(interp (lock_store_invariant m.locks) (heap_of_mem m));
  assert(interp (pts_to_array a full_permission (Seq.Base.create (U32.v len) init)) single_h);
  assert(interp ((pts_to_array a full_permission (Seq.Base.create (U32.v len) init))
    `star` (lock_store_invariant m.locks)) new_h);
  let new_m = { m with heap = new_h; ctr = m.ctr +1 } in
  (| a, new_m |)
#pop-options

#push-options "--z3rlimit 150 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1 --warn_error -271"
let alloc_array_is_frame_preserving
  (#t: _)
  (len:U32.t)
  (init: t)
  : Lemma (is_m_frame_preserving (alloc_array_pre_m_action len init))
  =
  is_m_frame_preserving_intro (alloc_array_pre_m_action len init) (fun frame m ->
    let h = heap_of_mem m in
    let a : array_ref t = {
      array_addr = m.ctr;
      array_max_length = len;
      array_length = len;
      array_offset = 0ul;
    } in
    let (| a, m1 |) = alloc_array_pre_m_action len init m in
    assert (m1.ctr = m.ctr + 1);
    assert (m1.locks == m.locks);
    let h1 = heap_of_mem m1 in
    let single_h = singleton_heap len init a in
    assert (h1 == join single_h h);
    intro_pts_to_array a full_permission (Seq.Base.create (U32.v len) init) single_h;
    assert (interp (pts_to_array a full_permission (Seq.Base.create (U32.v len) init)) single_h);
    assert (interp (frame `star` locks_invariant m) h);
    intro_star
      (pts_to_array a full_permission (Seq.Base.create (U32.v len) init))
      (frame `star` locks_invariant m)
      single_h
      h;
    assert (interp
      (pts_to_array a full_permission (Seq.Base.create (U32.v len) init) `star`
      (frame `star` locks_invariant m)) h1
    );
    star_associative
      (pts_to_array a full_permission (Seq.Base.create (U32.v len) init))
      frame
      (locks_invariant m);
    assert (interp
      (pts_to_array a full_permission (Seq.Base.create (U32.v len) init) `star`
      frame `star` locks_invariant m) h1
    )
  )
#pop-options

#push-options "--z3rlimit 150 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1 --warn_error -271"
let alloc_array_depends_only_on
  (#t: _)
  (len:U32.t)
  (init: t)
  : Lemma (m_action_depends_only_on (alloc_array_pre_m_action len init))
  =
  m_action_depends_only_on_intro (alloc_array_pre_m_action len init) (fun m0 h1 post ->
    let h0 = heap_of_mem m0 in
    let h = join h0 h1 in
    let m1 = { m0 with heap = h } in
    let (| x0, m |) = (alloc_array_pre_m_action len init) m0 in
    let (| x1, m' |) = (alloc_array_pre_m_action len init) m1 in
    alloc_array_is_frame_preserving len init;
    assert (x0 == x1);
    assert (disjoint (heap_of_mem m) h1);
    affine_star
      (pts_to_array x0 full_permission (Seq.Base.create (U32.v len) init))
      (locks_invariant m)
      (heap_of_mem m);
    assert (interp
      (pts_to_array x0 full_permission (Seq.Base.create (U32.v len) init))
      (heap_of_mem m)
    );
    assert (heap_of_mem m' == join (heap_of_mem m) h1)
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
  alloc_array_is_frame_preserving len init;
  alloc_array_depends_only_on len init;
  alloc_array_pre_m_action len init

let free_array_pre_action
  (#t: _)
  (a: array_ref t{freeable a})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  : pre_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> emp)
  = fun h -> (| (), h |)

let free_array_action
  (#t: _)
  (a: array_ref t{freeable a})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  =
  pre_action_to_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> emp)
    (free_array_pre_action a iseq)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 post -> ())
    (fun frame h0 h1 post -> ())

let free_array
  (#t: _)
  (a: array_ref t{freeable a})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  : m_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> emp)
  =
  non_alloc_action_to_non_locking_m_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> emp)
    (free_array_action a iseq)
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
            | Some (x, p) ->
              assert(perm `lesser_equal_permission` p);
              let new_p = sub_permissions p (half_permission perm) in
              Some (x, (new_p <: (perm:permission{allows_read perm})))
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
            | Some (x, _) ->
              Some (x, (half_permission perm <: (perm:permission{allows_read perm})))
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
    (fun frame h0 h1 post ->
      let (|x_alone, h0'|) = share_array_pre_action a iseq perm h0 in
      let (|x_joint, h'|) = share_array_pre_action a iseq perm (join h0 h1) in
      assert(x_alone == x_joint);
      assert(post x_alone h0' <==> post x_joint h')
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
    (fun frame h0 h1 post -> ())
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
    (fun frame h0 h1 post -> ())
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
    (fun frame h0 h1 post -> ())
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

#push-options "--max_fuel 2 --initial_fuel 2 --z3rlimit 20"
let get_ref
  (#t: Type0)
  (r: reference t)
  (p: permission{allows_read p})
  (contents: Ghost.erased t)
  : m_action
    (pts_to_ref r p contents)
    (x:t{x == Ghost.reveal contents})
    (fun _ -> pts_to_ref r p contents)
  =
  index_array r (Seq.create 1 (Ghost.reveal contents)) p 0ul
#pop-options

let set_ref
  (#t: Type0)
  (r: reference t)
  (contents: Ghost.erased t)
  (v: t)
  : m_action
    (pts_to_ref r full_permission contents)
    unit
    (fun _ -> pts_to_ref r full_permission v)
  =
  assert(Seq.upd (Seq.create 1 (Ghost.reveal contents)) 0 v `Seq.equal` Seq.create 1 v);
  upd_array r (Seq.create 1 (Ghost.reveal contents)) 0ul v

let alloc_ref
  (#t: Type0)
  (v: t)
  : m_action
    emp
    (reference t)
    (fun r -> pts_to_ref r full_permission v)
  =
  alloc_array 1ul v

let free_ref
  (#t: Type0)
  (r: reference t)
  (contents: Ghost.erased t)
  : m_action
    (pts_to_ref r full_permission contents)
    unit
    (fun _ -> emp)
  =
  free_array r (Seq.create 1 (Ghost.reveal contents))

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

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 60"
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
