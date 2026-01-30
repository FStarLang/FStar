(*
   Copyright 2023 Microsoft Research

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

module Pulse.Lib.Vec
#lang-pulse

open Pulse.Lib.Core
open Pulse.Lib.Pervasives

module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array

type vec a = A.array a
let length v = A.length v
let is_full_vec v = A.is_full_array v
let pts_to v #p s = A.pts_to v #p s
let pts_to_timeless _ _ _ = ()
let pts_to_len v = A.pts_to_len v

(* This function is extracted primitively. The implementation
below is only a model, and uses the internal Ref.alloc. Hence
we disable the warning about using Array.alloc. *)
#push-options "--warn_error -288"
let alloc x n = A.alloc x n
#pop-options
let op_Array_Access v i #p #s = A.op_Array_Access v i #p #s
let op_Array_Assignment v i x #s = A.op_Array_Assignment v i x #s
(* Same comment as above *)
#push-options "--warn_error -288"
let free v #s = A.free v #s
#pop-options
let share v = A.share v
let gather v = A.gather v

let vec_to_array v = v

ghost
fn to_array_pts_to (#a:Type0) (v:vec a) (#p:perm) (#s:Seq.seq a)
  requires pts_to v #p s
  ensures A.pts_to (vec_to_array v) #p s
{
  rewrite (pts_to v #p s) as
          (A.pts_to (vec_to_array v) #p s);
}

ghost
fn to_vec_pts_to (#a:Type0) (v:vec a) (#p:perm) (#s:Seq.seq a)
  requires A.pts_to (vec_to_array v) #p s
  ensures pts_to v #p s
{
   rewrite (A.pts_to (vec_to_array v) #p s)
        as (pts_to v #p s)

}

fn read_ref (#a:Type0) (r:R.ref (vec a)) (i:SZ.t)
  (#v:erased (vec a))
  (#s:(s:erased (Seq.seq a) { SZ.v i < Seq.length s }))
  requires R.pts_to r v
  requires pts_to v s
  returns x:a
  ensures R.pts_to r v ** pts_to v s ** pure (x == Seq.index s (SZ.v i))
{
  let vc = !r;
  rewrite (pts_to (reveal v) s)
       as (pts_to vc s);
  let x = op_Array_Access vc i;
  rewrite (pts_to vc s)
       as (pts_to (reveal v) s);
  x
}



fn write_ref (#a:Type0) (r:R.ref (vec a)) (i:SZ.t) (x:a)
  (#v:erased (vec a))
  (#s:(s:erased (Seq.seq a) { SZ.v i < Seq.length s }))
  requires R.pts_to r v
  requires pts_to v s
  ensures R.pts_to r v ** pts_to v (Seq.upd s (SZ.v i) x)
{
  let vc = !r;
  rewrite (pts_to (reveal v) s)
       as (pts_to vc s);
  op_Array_Assignment vc i x;
  with s. assert (pts_to vc s);
  rewrite (pts_to vc s)
       as (pts_to (reveal v) s)
}



fn replace_i (#a:Type0) (v:vec a) (i:SZ.t) (x:a)
  (#s:(s:erased (Seq.seq a) { SZ.v i < Seq.length s }))
  requires pts_to v s
  returns res:a
  ensures pts_to v (Seq.upd s (SZ.v i) x) ** pure (res == Seq.index s (SZ.v i))
{
  let y = op_Array_Access v i;
  op_Array_Assignment v i x;
  y
}



fn replace_i_ref (#a:Type0) (r:R.ref (vec a)) (i:SZ.t) (x:a)
  (#v:erased (vec a))
  (#s:erased (Seq.seq a) { SZ.v i < Seq.length s })
  requires R.pts_to r v
  requires pts_to v s
  returns res:a
  ensures R.pts_to r v ** pts_to v (Seq.upd s (SZ.v i) x) ** pure (res == Seq.index s (SZ.v i))
{
  let vc = !r;
  rewrite (pts_to v s)
       as (pts_to vc s);
  let y = op_Array_Access vc i;
  op_Array_Assignment vc i x;
  with #s. assert (pts_to vc s);
  rewrite (pts_to vc s)
       as (pts_to v s);
  y
}


fn compare
        (#t:eqtype)
        (l:SZ.t)
        (a1 a2:lvec t (SZ.v l))
        (#p1 #p2:perm)
        (#s1 #s2:Ghost.erased (Seq.seq t))
  requires
     pts_to a1 #p1 s1 **
     pts_to a2 #p2 s2
  returns res : bool
  ensures
     pts_to a1 #p1 s1 **
     pts_to a2 #p2 s2 **
     pure (res <==> Seq.equal s1 s2)
{
  unfold (pts_to a1 #p1 s1);
  unfold (pts_to a2 #p2 s2);
  let r = A.compare l a1 a2;
  fold (pts_to a1 #p1 s1);
  fold (pts_to a2 #p2 s2);
  r
}
