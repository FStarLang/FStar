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
open Steel.Memory
open FStar.Real
open Steel.Permissions
module U32 = FStar.UInt32

let depends_only_on_without_affinity (q:heap -> prop) (fp:hprop) =
  (forall (h0:hheap fp) (h1:heap{disjoint h0 h1}). q h0 <==> q (join h0 h1))

let preserves_frame_prop (frame:hprop) (h0 h1:heap) =
  forall (q:(heap -> prop){q `depends_only_on_without_affinity` frame}).
    q h0 <==> q h1

let pre_action (fp:hprop) (a:Type) (fp':a -> hprop) =
  hheap fp -> (x:a & hheap (fp' x))

let is_frame_preserving #a #fp #fp' (f:pre_action fp a fp') =
  forall frame h0.
    interp (fp `star` frame) h0 ==>
    (let (| x, h1 |) = f h0 in
     interp (fp' x `star` frame) h1 /\
     preserves_frame_prop frame h0 h1)

let action_depends_only_on_fp (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_action fp a fp')
  = forall (h0:hheap fp)
      (h1:heap {disjoint h0 h1})
      (post: (x:a -> fp_prop (fp' x))).
      (interp fp (join h0 h1) /\ (
       let (| x0, h |) = f h0 in
       let (| x1, h' |) = f (join h0 h1) in
       x0 == x1 /\
       (post x0 h <==> post x1 h')))

let action (fp:hprop) (a:Type) (fp':a -> hprop) =
  f:pre_action fp a fp'{ is_frame_preserving f /\
                         action_depends_only_on_fp f }


let pre_m_action (fp:hprop) (a:Type) (fp':a -> hprop) =
  hmem fp -> (x:a & hmem (fp' x))

val m_action_depends_only_on (#pre:hprop) (#a:Type) (#post:a -> hprop) (f:pre_m_action pre a post) : prop

val is_m_frame_preserving (#a:Type) (#fp:hprop) (#fp':a -> hprop) (f:pre_m_action fp a fp') : prop

let m_action (fp:hprop) (a:Type) (fp':a -> hprop) =
  f:pre_m_action fp a fp'{ is_m_frame_preserving f /\ m_action_depends_only_on f }

val frame_fp_prop (#fp:_) (#a:Type) (#fp':_) (act:action fp a fp')
                  (#frame:hprop) (q:fp_prop frame)
   : Lemma (forall (h0:hheap (fp `star` frame)).
              (affine_star fp frame h0;
               q h0 ==>
               (let (| x, h1 |) = act h0 in
                q h1)))

////////////////////////////////////////////////////////////////////////////////
// Arrays
////////////////////////////////////////////////////////////////////////////////

val as_seq (#t:_) (a:array_ref t) (m:hheap (array a))
  : (Seq.lseq t (U32.v (length a)))

/// as_seq respect pts_to_array
val as_seq_lemma
  (#t:_)
  (a:array_ref t)
  (i:U32.t{U32.v i < U32.v (length a)})
  (p:permission{allows_read p})
  (m:hheap (array_perm a p))
  : Lemma (interp (array a) m /\
           interp (pts_to_array a p (as_seq a m)) m)

val index_array
  (#t:_)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: permission{allows_read p})
  (i:U32.t{U32.v i < U32.v (length a)})
  : m_action
    (pts_to_array a p iseq)
    (x:t{x == Seq.index iseq (U32.v i)})
    (fun _ -> pts_to_array a p iseq)

val upd_array
  (#t:_)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  : m_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> pts_to_array a full_permission (Seq.upd iseq (U32.v i) v))

val alloc_array
  (#t: _)
  (len:U32.t)
  (init: t)
  : m_action
    emp
    (a:array_ref t{length a = len /\ offset a = 0ul /\ max_length a = len})
    (fun a -> pts_to_array a full_permission (Seq.Base.create (U32.v len) init))

val free_array
  (#t: _)
  (a: array_ref t{freeable a})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  : m_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> emp)

val share_array
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: permission{allows_read p})
  : m_action
    (pts_to_array a p iseq)
    (a':array_ref t{
      length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
      address a = address a'
    })
    (fun a' -> star
      (pts_to_array a (half_permission p) iseq)
      (pts_to_array a' (half_permission p) (Ghost.hide (Ghost.reveal iseq)))
    )

val gather_array
  (#t: _)
  (a: array_ref t)
  (a':array_ref t{
    length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
    address a = address a'
  })
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: permission{allows_read p})
  : m_action
    (star
      (pts_to_array a (half_permission p) iseq)
      (pts_to_array a' (half_permission p) (Ghost.hide (Ghost.reveal iseq)))
    )
    unit
    (fun _ -> pts_to_array a p iseq)

val split_array
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

val glue_array
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

///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// References
///////////////////////////////////////////////////////////////////////////////

val sel_ref (#t: Type0) (r: reference t) (h: hheap (ref r)) : t

val sel_ref_lemma
  (t: Type0)
  (p: permission{allows_read p})
  (r: reference t)
  (m: hheap (ref_perm r p))
  : Lemma (interp (ref r) m /\ interp (pts_to_ref r p (sel_ref r m)) m)

val get_ref
  (#t: Type0)
  (r: reference t)
  (p: permission{allows_read p})
  (contents: Ghost.erased t)
  : m_action
    (pts_to_ref r p contents)
    (x:t{x == Ghost.reveal contents})
    (fun _ -> pts_to_ref r p contents)

val set_ref
  (#t: Type0)
  (r: reference t)
  (contents: Ghost.erased t)
  (v: t)
  : m_action
    (pts_to_ref r full_permission contents)
    unit
    (fun _ -> pts_to_ref r full_permission v)

val alloc_ref
  (#t: Type0)
  (v: t)
  : m_action
    emp
    (reference t)
    (fun r -> pts_to_ref r full_permission v)

val free_ref
  (#t: Type0)
  (r: reference t)
  (contents: Ghost.erased t)
  : m_action
    (pts_to_ref r full_permission contents)
    unit
    (fun _ -> emp)

val share_ref
  (#t: Type0)
  (r: reference t)
  (p: permission{allows_read p})
  (contents: Ghost.erased t)
  : m_action
    (pts_to_ref r p contents)
    (r':reference t{ref_address r' = ref_address r})
    (fun r' ->
      pts_to_ref r (half_permission p) contents `star`
      pts_to_ref r (half_permission p) contents
    )

val gather_ref
  (#t: Type0)
  (r: reference t)
  (r':reference t{ref_address r' = ref_address r})
  (p: permission{allows_read p})
  (contents: Ghost.erased t)
  : m_action
    (pts_to_ref r (half_permission p) contents `star`
      pts_to_ref r (half_permission p) contents)
    unit
    (fun _ -> pts_to_ref r p contents)

///////////////////////////////////////////////////////////////////////////////
// Locks
///////////////////////////////////////////////////////////////////////////////

val lock (p:hprop) : Type0

val new_lock (p:hprop)
  : m_action p (lock p) (fun _ -> emp)

val mem_evolves  : Preorder.preorder mem
