(*
   Copyright 2025 Microsoft Research

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

module Pulse.Lib.ResizableVec

#lang-pulse

open Pulse.Lib.Pervasives
module Seq = FStar.Seq
module SZ = FStar.SizeT
module V = Pulse.Lib.Vec
module Box = Pulse.Lib.Box
open Pulse.Lib.Box

/// Internal representation
noeq
type rvec_internal (t:Type0) = {
  vec_box: box (V.vec (option t));
  size_box: box SZ.t;
  cap_box: box SZ.t;
}

let rvec t = rvec_internal t

/// Buffer well-formedness: first len elements are Some
let buf_wf (#t:Type0) (buf:Seq.seq (option t)) (len:nat) : prop =
  len <= Seq.length buf /\
  (forall (i:nat). i < len ==> Some? (Seq.index buf i))

/// Extract values from well-formed buffer
let get_elem (#t:Type0) (buf:Seq.seq (option t)) (len:nat) (i:nat)
  : Pure t (requires buf_wf buf len /\ i < len) (ensures fun _ -> True)
  = Some?.v (Seq.index buf i)

let extract_seq (#t:Type0) (buf:Seq.seq (option t)) (len:nat)
  : Pure (Seq.seq t) (requires buf_wf buf len) (ensures fun s -> Seq.length s == len)
  = Seq.init #t len (fun i -> get_elem buf len i)

let extract_seq_index (#t:Type0) (buf:Seq.seq (option t)) (len:nat{buf_wf buf len}) (i:nat{i < len})
  : Lemma (Seq.index (extract_seq buf len) i == Some?.v (Seq.index buf i))
  = ()

let buf_wf_upd (#t:Type0) (buf:Seq.seq (option t)) (len:nat) (i:nat) (x:t)
  : Lemma (requires buf_wf buf len /\ i < Seq.length buf)
          (ensures buf_wf (Seq.upd buf i (Some x)) len)
  = ()

let buf_wf_extend (#t:Type0) (buf:Seq.seq (option t)) (len:nat) (x:t)
  : Lemma (requires buf_wf buf len /\ len < Seq.length buf)
          (ensures buf_wf (Seq.upd buf len (Some x)) (len + 1))
  = ()

/// The is_rvec predicate - now includes capacity
let is_rvec #t (v:rvec t) (s:Seq.seq t) (cap:nat) : slprop =
  exists* (vec:V.vec (option t)) (buf:Seq.seq (option t)) (sz:SZ.t) (cap_sz:SZ.t).
    pts_to v.vec_box vec **
    pts_to v.size_box sz **
    pts_to v.cap_box cap_sz **
    V.pts_to vec buf **
    pure (
      SZ.v sz == Seq.length s /\
      SZ.v cap_sz == Seq.length buf /\
      SZ.v cap_sz == cap /\
      SZ.v sz <= cap /\
      cap > 0 /\
      V.is_full_vec vec /\
      buf_wf buf (SZ.v sz) /\
      s `Seq.equal` extract_seq buf (SZ.v sz)
    )

/// Create
fn create (#t:Type0) (capacity:SZ.t{SZ.v capacity > 0})
  requires emp
  returns v:rvec t
  ensures is_rvec v Seq.empty (SZ.v capacity)
{
  let vec = V.alloc #(option t) None capacity;
  let vec_box : box (V.vec (option t)) = alloc vec;
  let size_box : box SZ.t = alloc 0sz;
  let cap : SZ.t = capacity;  // cast to remove refinement
  let cap_box : box SZ.t = alloc cap;
  
  let v : rvec_internal t = Mkrvec_internal #t vec_box size_box cap_box;
  
  V.pts_to_len vec;
  
  rewrite (pts_to vec_box vec) as (pts_to v.vec_box vec);
  rewrite (pts_to size_box 0sz) as (pts_to v.size_box 0sz);
  rewrite (pts_to cap_box cap) as (pts_to v.cap_box cap);
  
  fold (is_rvec v Seq.empty (SZ.v capacity));
  v
}

/// Length
fn len (#t:Type0) (v:rvec t) (#s:erased (Seq.seq t)) (#cap:erased nat)
  requires is_rvec v s cap
  returns n:SZ.t
  ensures is_rvec v s cap ** pure (SZ.v n == Seq.length s)
{
  unfold (is_rvec v s cap);
  with vec buf sz cap_sz. _;
  let n = op_Bang v.size_box;
  fold (is_rvec v s cap);
  n
}

/// Get capacity
fn get_capacity (#t:Type0) (v:rvec t) (#s:erased (Seq.seq t)) (#cap:erased nat)
  requires is_rvec v s cap
  returns n:SZ.t
  ensures is_rvec v s cap ** pure (SZ.v n == cap)
{
  unfold (is_rvec v s cap);
  with vec buf sz cap_sz. _;
  let n = op_Bang v.cap_box;
  fold (is_rvec v s cap);
  n
}

/// Get element
fn get (#t:Type0) (v:rvec t) (i:SZ.t) (#s:erased (Seq.seq t){SZ.v i < Seq.length s}) (#cap:erased nat)
  requires is_rvec v s cap
  returns x:t
  ensures is_rvec v s cap ** pure (x == Seq.index s (SZ.v i))
{
  unfold (is_rvec v s cap);
  with vec buf sz cap_sz. _;
  
  let current_vec = op_Bang v.vec_box;
  rewrite (V.pts_to vec buf) as (V.pts_to current_vec buf);
  
  let opt_x = V.op_Array_Access current_vec i;
  let x = Some?.v opt_x;
  
  rewrite (V.pts_to current_vec buf) as (V.pts_to vec buf);
  extract_seq_index buf (SZ.v sz) (SZ.v i);
  fold (is_rvec v s cap);
  x
}

/// Set element
fn set (#t:Type0) (v:rvec t) (i:SZ.t) (x:t) (#s:erased (Seq.seq t){SZ.v i < Seq.length s}) (#cap:erased nat)
  requires is_rvec v s cap
  ensures is_rvec v (Seq.upd s (SZ.v i) x) cap
{
  unfold (is_rvec v s cap);
  with vec buf sz cap_sz. _;
  
  let current_vec = op_Bang v.vec_box;
  rewrite (V.pts_to vec buf) as (V.pts_to current_vec buf);
  
  V.op_Array_Assignment current_vec i (Some x);
  with buf'. _;
  rewrite (V.pts_to current_vec buf') as (V.pts_to vec buf');
  
  buf_wf_upd buf (SZ.v sz) (SZ.v i) x;
  fold (is_rvec v (Seq.upd s (SZ.v i) x) cap);
  ()
}

/// Check if there is room
fn has_room (#t:Type0) (v:rvec t) (#s:erased (Seq.seq t)) (#cap:erased nat)
  requires is_rvec v s cap
  returns b:bool
  ensures is_rvec v s cap ** pure (b <==> Seq.length s < cap)
{
  unfold (is_rvec v s cap);
  with vec buf sz cap_sz. _;
  let current_sz = op_Bang v.size_box;
  let current_cap = op_Bang v.cap_box;
  let b = SZ.lt current_sz current_cap;
  fold (is_rvec v s cap);
  b
}

/// Push - returns true if successful, false if at capacity
fn push (#t:Type0) (v:rvec t) (x:t) (#s:erased (Seq.seq t)) (#cap:erased nat)
  requires is_rvec v s cap
  returns b:bool
  ensures (if b then is_rvec v (Seq.snoc s x) cap ** pure (Seq.length s < cap)
           else is_rvec v s cap ** pure (Seq.length s == cap))
{
  unfold (is_rvec v s cap);
  with vec buf sz cap_sz. _;
  
  let current_sz = op_Bang v.size_box;
  let current_cap = op_Bang v.cap_box;
  let current_vec = op_Bang v.vec_box;
  
  rewrite (V.pts_to vec buf) as (V.pts_to current_vec buf);
  
  // Check if we have room
  if (SZ.lt current_sz current_cap) {
    V.op_Array_Assignment current_vec current_sz (Some x);
    with buf'. _;
    
    ( := ) v.size_box (SZ.add current_sz 1sz);
    
    rewrite (V.pts_to current_vec buf') as (V.pts_to vec buf');
    buf_wf_extend buf (SZ.v sz) x;
    fold (is_rvec v (Seq.snoc s x) cap);
    true
  } else {
    // No room - at capacity
    rewrite (V.pts_to current_vec buf) as (V.pts_to vec buf);
    fold (is_rvec v s cap);
    false
  }
}

/// Pop
fn pop (#t:Type0) (v:rvec t) (#s:erased (Seq.seq t){Seq.length s > 0}) (#cap:erased nat)
  requires is_rvec v s cap
  returns x:t
  ensures is_rvec v (Seq.slice s 0 (Seq.length s - 1)) cap ** 
          pure (x == Seq.index s (Seq.length s - 1))
{
  unfold (is_rvec v s cap);
  with vec buf sz cap_sz. _;
  
  let current_sz = op_Bang v.size_box;
  let last_idx = SZ.sub current_sz 1sz;
  
  let current_vec = op_Bang v.vec_box;
  rewrite (V.pts_to vec buf) as (V.pts_to current_vec buf);
  
  let opt_x = V.op_Array_Access current_vec last_idx;
  let x = Some?.v opt_x;
  
  ( := ) v.size_box last_idx;
  
  rewrite (V.pts_to current_vec buf) as (V.pts_to vec buf);
  extract_seq_index buf (SZ.v sz) (SZ.v last_idx);
  fold (is_rvec v (Seq.slice s 0 (Seq.length s - 1)) cap);
  x
}

/// Free
fn free (#t:Type0) (v:rvec t) (#s:erased (Seq.seq t)) (#cap:erased nat)
  requires is_rvec v s cap
  ensures emp
{
  unfold (is_rvec v s cap);
  with vec buf sz cap_sz. _;
  
  let current_vec = op_Bang v.vec_box;
  rewrite (V.pts_to vec buf) as (V.pts_to current_vec buf);
  
  V.free current_vec;
  free v.vec_box;
  free v.size_box;
  free v.cap_box;
  ()
}
