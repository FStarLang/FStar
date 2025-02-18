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

module Pulse.Lib.AnchoredReference
#lang-pulse
open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Ghost
open FStar.Preorder
open PulseCore.Preorder
open Pulse.Lib.FractionalAnchoredPreorder
module FRAP = Pulse.Lib.FractionalAnchoredPreorder
module GPR = Pulse.Lib.GhostPCMReference
module T = FStar.Tactics

let carrier (#a:Type0) (#p:preorder a) (#anc:anchor_rel p)
: Type0
= FRAP.knowledge #a #p anc

let ref ([@@@unused]a:Type u#0) (p : preorder a) (anc : anchor_rel p)
: Type u#0
= GPR.gref (FRAP.pcm #a #p #anc)

instance ref_non_informative (a:Type0) (p : preorder a) (anc : anchor_rel p)
: NonInformative.non_informative (ref a p anc)
= { reveal = (fun (x:erased (ref a p anc)) -> FStar.Ghost.reveal x)}

[@@pulse_unfold]
let core_pts_to
  (#a:Type) (#p:preorder a) (#anc:anchor_rel p)
  (r:ref a p anc)
  (#[T.exact (`1.0R)] q:perm)
  (n:a)
  (with_anchor:bool)
: p:slprop { timeless p }
= exists* (k:FRAP.knowledge anc) .
    GPR.pts_to r k **
    pure (fractional_ownership_maybe_with_anchor q n with_anchor with_anchor k)

let pts_to_full
  (#a:Type) (#p:preorder a) (#anc:anchor_rel p)
  (r:ref a p anc)
  (#[T.exact (`1.0R)] q:perm)
  (n:a)
: p:slprop { timeless p }
= core_pts_to r #q n true

let pts_to
  (#a:Type) (#p:preorder a) (#anc:anchor_rel p)
  (r:ref a p anc)
  (#[T.exact (`1.0R)] q:perm)
  (n:a)
: p:slprop { timeless p }
= core_pts_to r #q n false

let anchored
  (#a:Type)
  (#p:_)
  (#anc:_)
  (r:ref a p anc)
  (n:a) 
: p:slprop{timeless p}
= exists* (k:FRAP.knowledge anc) .
    GPR.pts_to r k **
    pure (owns_only_anchor n k)

let snapshot (#a:Type) (#p:_) (#anc:_) (r : ref a p anc) (n:a)
: p:slprop { timeless p }
= exists* (k:FRAP.knowledge anc) .
    GPR.pts_to r k **
    pure (snapshot_pred n k)

let init_val (#a:Type) (#p:_) (anc:anchor_rel p) (x:a { anc x x })
: v:FRAP.knowledge anc { fractional_ownership_maybe_with_anchor 1.0R x true true v }
= let perm = (Some 1.0R, (Some x)) in
  let hist = [ x ] in
  Owns (perm, hist)

ghost
fn alloc (#a:Type) (x:a) (#p:_) (#anc:anchor_rel p)
requires pure (anc x x)
returns r:ref a p anc
ensures pts_to_full r x
{
  let r = GPR.alloc #_ #(FRAP.pcm #a #p #anc) (init_val anc x);
  fold (pts_to_full r x);
  r
}

ghost
fn share (#a:Type) (#p:_) (#anc:_) (r:ref a p anc) (#f: perm) (#v:erased a)
requires pts_to r #f v
ensures pts_to r #(f /. 2.0R) v ** pts_to r #(f /. 2.0R) v
{
  unfold (pts_to r #f v);
  with k. assert (GPR.pts_to r k);
  let split = half_frac #a #p #anc f v k;
  rewrite (GPR.pts_to r k)
  as (GPR.pts_to r (split `FStar.PCM.op (FRAP.pcm #a #p #anc)` split));
  GPR.share r split split;
  fold (pts_to r #(f /. 2.0R) v);
  fold (pts_to r #(f /. 2.0R) v)
}

ghost
fn gather (#a:Type) (#p:_) (#anc:_) (r:ref a p anc) (#v1 #v2:erased a) (#f1 #f2: perm)
requires pts_to r #f1 v1 ** pts_to r #f2 v2
ensures pts_to r #(f1 +. f2) v1 ** pure (v1 == v2)
{
  unfold (pts_to r #f1 v1);
  unfold (pts_to r #f2 v2);
  GPR.gather r _ _;
  fold (pts_to r #(f1 +. f2) v1);
}

ghost
fn write (#a:Type) (#p:_) (#anc:_) (r:ref a p anc) (#v:erased a) (w : erased a)
requires pts_to r v ** pure (p v w /\ (forall anchor. anc anchor v ==> anc anchor w))
ensures pts_to r w
{
  unfold (pts_to r v);
  with k0. assert (GPR.pts_to r k0);
  GPR.write r k0 _ (update_ownership #_ #p #anc v w k0);
  fold (pts_to r w);
}

ghost
fn write_full (#a:Type) (#p:_) (#anc:_) (r:ref a p anc) (#v:erased a) (w : erased a)
requires pts_to_full r v ** pure (p v w /\ anc w w)
ensures pts_to_full r w
{
  unfold (pts_to_full r v);
  with k0. assert (GPR.pts_to r k0);
  GPR.write r k0 _ (update_full_ownership #_ #p #anc v w true k0);
  fold (pts_to_full r w);
}

ghost
fn leave_anchor_pts_to 
      (#a:Type) (#p:_) (#anc:anchor_rel p) 
      (r : ref a p anc) (v:a) (k:FRAP.knowledge anc { fractional_ownership_maybe_with_anchor 1.0R v true true k })
requires GPR.pts_to r (leave_anchor 1.0R v true true k)
ensures pts_to r v
{
  fold (pts_to r v)
}

ghost
fn drop_anchor (#a:Type) (#p:_) (#anc:anchor_rel p) (r : ref a p anc) (#v:a)
requires pts_to_full r v
ensures pts_to r v ** anchored r v
{
  unfold (pts_to_full r v);
  with k. assert (GPR.pts_to r k);
  share_anchor #a #p #anc 1.0R v k;
  rewrite (GPR.pts_to r k)
  as (GPR.pts_to r (leave_anchor 1.0R v true true k `FStar.PCM.op (FRAP.pcm #a #p #anc)` take_anchor 1.0R v true true k));
  GPR.share r (leave_anchor 1.0R v true true k) (take_anchor 1.0R v true true k);
  leave_anchor_pts_to r v k;
  fold (anchored r v);
}

ghost
fn unfold_anchored (#a:Type) (#p:_) (#anc:anchor_rel p) (r : ref a p anc) (#v:a)
requires anchored r v
returns k:FRAP.knowledge anc
ensures GPR.pts_to r k ** pure (owns_only_anchor v k)
{
  unfold (anchored r v);
  with k. assert (GPR.pts_to r k);
  k
}

ghost
fn fold_anchored (#a:Type) (#p:_) (#anc:anchor_rel p) (r : ref a p anc) (#v:a) (k:FRAP.knowledge anc)
requires GPR.pts_to r k ** pure (owns_only_anchor v k)
ensures anchored r v
{
  fold (anchored r v)
}


ghost
fn lift_anchor (#a:Type) (#p:_) (#anc:anchor_rel p) (r : ref a p anc) (#v:a) (va:a)
requires pts_to r v ** anchored r va ** pure (anc v v)
ensures pts_to_full r v ** pure (anc va v /\ True)
{
  unfold (pts_to r v);
  with k0. assert (GPR.pts_to r k0);
  let k1 = unfold_anchored r;
  GPR.gather r k0 k1;
  gather_anchor 1.0R v va k0 k1;
  GPR.write r _ _ (update_full_ownership v v false _);
  fold (pts_to_full r v);
}

ghost
fn recall_anchor (#a:Type) (#p:_) (#anc:anchor_rel p) (r : ref a p anc) (#v:a) (va:a) (#f:perm)
requires pts_to r #f v ** anchored r va
ensures pts_to r #f v ** anchored r va ** pure (anc va v)
{
  unfold (pts_to r #f v);
  with k0. assert (GPR.pts_to r k0);
  let k1 = unfold_anchored r;
  GPR.gather r k0 k1;
  gather_anchor f v va k0 k1;
  GPR.share r k0 k1;
  fold_anchored r #va k1;
  fold (pts_to r #f v)
}

ghost
fn unfold_snapshot (#a:Type) (#p:_) (#anc:_) (r : ref a p anc) (#v:a)
requires snapshot r v
returns k:FRAP.knowledge anc
ensures GPR.pts_to r k ** pure (snapshot_pred v k)
{
  unfold (snapshot r v);
  with k. assert (GPR.pts_to r k);
  k
}

ghost
fn fold_snapshot (#a:Type) (#p:_) (#anc:_) (r : ref a p anc) (#v:a) (k:FRAP.knowledge anc)
requires GPR.pts_to r k ** pure (snapshot_pred v k)
ensures snapshot r v
{
  fold (snapshot r v)
}

ghost
fn dup_snapshot (#a:Type) (#p:_) (#anc:anchor_rel p) (r : ref a p anc) (#v:a)
requires snapshot r v
ensures snapshot r v ** snapshot r v
{
  unfold snapshot;
  with k. assert (GPR.pts_to r k);
  rewrite (GPR.pts_to r k)
      as  (GPR.pts_to r (k `FStar.PCM.op (FRAP.pcm #a #p #anc)` k));
  GPR.share r k k;
  fold_snapshot r #v k;
  fold_snapshot r #v k
}

ghost
fn take_snapshot_core (#a:Type) (#p:_) (#f:perm) (#anc:anchor_rel p) (r : ref a p anc) (#b:bool) (#v:a)
requires core_pts_to r #f v b
ensures  core_pts_to r #f v b ** snapshot r v
{
  with k. assert (GPR.pts_to r k);
  rewrite (GPR.pts_to r k)
      as  (GPR.pts_to r (k `FStar.PCM.op (FRAP.pcm #a #p #anc)` (snapshot_knowledge k)));
  GPR.share r k (snapshot_knowledge k);
  fold_snapshot r #v (snapshot_knowledge k);
}
  
  
ghost
fn take_snapshot (#a:Type) (#p:_) (#f:perm) (#anc:anchor_rel p) (r : ref a p anc) (#v:a)
requires pts_to r #f v
ensures  pts_to r #f v ** snapshot r v
{
  unfold (pts_to r #f v);
  take_snapshot_core #a #p #f r #false #v;
  fold (pts_to r #f v);
}

ghost
fn take_snapshot_full (#a:Type) (#p:_) (#f:perm) (#anc:anchor_rel p) (r : ref a p anc) (#v:a)
requires pts_to_full r #f v
ensures  pts_to_full r #f v ** snapshot r v
{
  unfold (pts_to_full r #f v);
  take_snapshot_core #a #p #f r #true #v;
  fold (pts_to_full r #f v);
}

ghost
fn recall_snapshot (#a:Type) (#p:_) (#anc:anchor_rel p) (r : ref a p anc) #f (#v0 #v:a)
requires pts_to r #f v ** snapshot r v0
ensures  pts_to r #f v ** snapshot r v0 ** pure (p v0 v /\ True)
{
  unfold (pts_to r #f v);
  with k. assert (GPR.pts_to r k);
  let k1 = unfold_snapshot r;
  GPR.gather r k k1;
  GPR.share r k k1;
  fold_snapshot r #v0 k1;
  fold (pts_to r #f v);
}