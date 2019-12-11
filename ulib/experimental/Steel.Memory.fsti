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
module Steel.Memory
open Steel.Heap
open Steel.HProp
open FStar.Real
open Steel.Permissions
module U32 = FStar.UInt32

include Steel.Heap
include Steel.HProp

////////////////////////////////////////////////////////////////////////////////
// Memory
////////////////////////////////////////////////////////////////////////////////
val mem : Type u#1
val locks_invariant : mem -> hprop

val heap_of_mem (x:mem) : heap

val m_disjoint: mem -> heap -> prop

val upd_joined_heap: (m:mem) -> (h:heap{m_disjoint m h}) -> mem

let hmem (fp:hprop) = m:mem{interp (fp `star` locks_invariant m) (heap_of_mem m)}

////////////////////////////////////////////////////////////////////////////////
// Actions:
// sel, split, update
////////////////////////////////////////////////////////////////////////////////
let pre_action (fp:hprop) (a:Type) (fp':a -> hprop) =
  hheap fp -> (x:a & hheap (fp' x))

let is_frame_preserving #a #fp #fp' (f:pre_action fp a fp') =
  forall frame h0.
    interp (fp `star` frame) h0 ==>
    (let (| x, h1 |) = f h0 in
     interp (fp' x `star` frame) h1)

let action_depends_only_on_fp (#pre:_) (#a:_) (#post:_) (f:pre_action pre a post)
  = forall (h0:hheap pre)
      (h1:heap {disjoint h0 h1})
      (post: (x:a -> fp_prop (post x))).
      (interp pre (join h0 h1) /\ (
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

val sel (#a:_) (r:ref a) (m:hheap (ptr r))
  : a

/// sel respect pts_to
val sel_lemma (#a:_) (r:ref a) (p:permission) (m:hheap (ptr_perm r p))
  : Lemma (interp (ptr r) m /\
           interp (pts_to r p (sel r m)) m)

/// memories satisfying [p1 `star` p2] can be split
/// into disjoint fragments satisfying each of them
val split_mem (p1 p2:hprop) (m:hheap (p1 `star` p2))
  : Tot (ms:(hheap p1 & hheap p2){
            let m1, m2 = ms in
            disjoint m1 m2 /\
            m == join m1 m2})

/// upd requires a full permission
val upd (#a:_) (r:ref a) (v:a)
  : m_action (ptr_perm r full_permission) unit (fun _ -> pts_to r full_permission v)


val upd_array
  (#t:_)
  (a:array_ref t)
  (iseq: Seq.lseq t (U32.v (length a)))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  : m_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> pts_to_array a full_permission (Seq.upd iseq (U32.v i) v))



val alloc (#a:_) (v:a)
  : m_action emp (ref a) (fun x -> pts_to x full_permission v)

val lock (p:hprop) : Type0

val new_lock (p:hprop)
  : m_action p (lock p) (fun _ -> emp)
