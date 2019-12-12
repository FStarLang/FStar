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
module Steel.Actions.Array
open Steel.Heap
open Steel.HProp
open FStar.Real
open Steel.Permissions
open Steel.Actions
module U32 = FStar.UInt32
open FStar.FunctionalExtensionality

friend Steel.Heap
friend Steel.HProp
friend Steel.Memory
friend Steel.Actions

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"



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
        let new_seq = Seq.upd seq (U32.v i + U32.v a.array_offset) (v, perm) in
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

#push-options "--z3rlimit 10 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
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
  let aux (addr: addr) : Lemma (
    let h0' = upd_array_seq' a iseq i v h0 in
    disjoint_addr h0' h1 addr
  ) =
    let h0' = upd_array_seq' a iseq i v h0 in
    match h0' addr, h1 addr, h0 addr with
    | Some (Array t0' len0' seq0'), Some (Array t1 len1 seq1),
      Some (Array t0 len0 seq0) ->
      if addr = a.array_addr then begin
        let aux (i':nat{i' < U32.v (length a)}) : Lemma (False) =
          let (x0, p0) = Seq.index seq0 (U32.v a.array_offset + i') in
          let (x1, p1) = Seq.index seq1 ( U32.v a.array_offset +i') in
          assert(Permission?.r p0 +. Permission?.r p1 <=. 1.0R);
          assert(full_permission `lesser_equal_permission` p0);
          assert(Permission?.r p1 = 0.0R);
          assert(Permission?.r p1 >. 0.0R)
        in
        if U32.v (length a) = 0 then () else aux 0
      end else begin
        ()
      end
    | _ -> ()
  in
  Classical.forall_intro aux
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

#push-options "--z3rlimit 80 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
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
      interp (pts_to_array a full_permission (Seq.upd iseq (U32.v i) v)  `star` frame) h1))
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
          interp (pts_to_array a full_permission (Seq.upd iseq (U32.v i) v) `star` frame) h1))
        [SMTPat ()]
      = upd_array_lemma' a iseq i v h frame
   in
   ()
#pop-options

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
  =
  let aux (addr: addr) : Lemma (
    let (| _, h |) = upd_array_heap a iseq i v h0 in
    disjoint_addr h h1 addr
  ) =
    let (| _, h |) = upd_array_heap a iseq i v h0 in
    match h addr, h1 addr, h0 addr with
    | Some (Array t len seq), Some (Array t1 len1 seq1),
      Some (Array t0 len0 seq0) ->
      if addr = a.array_addr then begin
        let aux (i':nat{i' < U32.v (length a)}) : Lemma (False) =
          let (x0, p0) = Seq.index seq0 (U32.v a.array_offset + i') in
          let (x1, p1) = Seq.index seq1 ( U32.v a.array_offset +i') in
          assert(Permission?.r p0 +. Permission?.r p1 <=. 1.0R);
          assert(full_permission `lesser_equal_permission` p0);
          assert(Permission?.r p1 = 0.0R);
          assert(Permission?.r p1 >. 0.0R)
        in
        if U32.v (length a) = 0 then () else aux 0
      end else begin
        ()
      end
    | _ -> ()
  in
  Classical.forall_intro aux

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

#push-options "--z3rlimit 100 --max_fuel 2 --initial_fuel 2"
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
