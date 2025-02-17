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
open Pulse.Lib.Pervasives
open PulseCore.FractionalPermission
open FStar.Ghost
open FStar.Preorder
open Pulse.Lib.FractionalAnchoredPreorder
#lang-pulse

module T = FStar.Tactics

[@@erasable]
val ref ([@@@unused]a:Type u#0) (p : preorder a) (anc : anchor_rel p) : Type u#0

instance val ref_non_informative (a:Type0) (p : preorder a) (anc : anchor_rel p)
  : NonInformative.non_informative (ref a p anc)

val pts_to_full
  (#a:Type) (#p:_) (#anc:_)
  ([@@@mkey]r:ref a p anc)
  (#[T.exact (`1.0R)] p:perm)
  (n:a)
: p:slprop { timeless p }

val pts_to
  (#a:Type) (#p:_) (#anc:_)
  ([@@@mkey]r:ref a p anc)
  (#[T.exact (`1.0R)] p:perm)
  (n:a)
: p:slprop { timeless p }

val anchored
  (#a:Type)
  (#p:_)
  (#anc:_)
  (r:ref a p anc)
  (n:a)
: p:slprop{ timeless p }

val snapshot (#a:Type) (#p:_) (#anc:_) (r : ref a p anc) (v:a)
: p:slprop { timeless p }


ghost
fn alloc (#a:Type) (x:a) (#p:_) (#anc:anchor_rel p)
requires pure (anc x x)
returns r:ref a p anc
ensures pts_to_full r x

ghost
fn share (#a:Type) (#p:_) (#anc:_) (r:ref a p anc) (#f: perm) (#v:erased a)
requires pts_to r #f v
ensures  pts_to r #(f /. 2.0R) v ** pts_to r #(f /. 2.0R) v

[@@allow_ambiguous]
ghost
fn gather (#a:Type) (#p:_) (#anc:_) (r:ref a p anc) (#v1 #v2:erased a) (#f1 #f2: perm)
requires pts_to r #f1 v1 ** pts_to r #f2 v2
ensures pts_to r #(f1 +. f2) v1 ** pure (v1 == v2)

ghost
fn write (#a:Type) (#p:_) (#anc:_) (r:ref a p anc) (#v:erased a) (w : erased a)
requires pts_to r v ** pure (p v w /\ (forall anchor. anc anchor v ==> anc anchor w))
ensures pts_to r w

ghost
fn write_full (#a:Type) (#p:_) (#anc:_) (r:ref a p anc) (#v:erased a) (w : erased a)
requires pts_to_full r v ** pure (p v w /\ anc w w)
ensures pts_to_full r w

ghost
fn drop_anchor (#a:Type) (#p:_) (#anc:anchor_rel p) (r : ref a p anc) (#v:a)
requires pts_to_full r v
ensures pts_to r v ** anchored r v

ghost
fn lift_anchor (#a:Type) (#p:_) (#anc:anchor_rel p) (r : ref a p anc) (#v:a) (va:a)
requires pts_to r v ** anchored r va ** pure (anc v v)
ensures pts_to_full r v ** pure (anc va v /\ True)

ghost
fn recall_anchor (#a:Type) (#p:_) (#anc:anchor_rel p) (r : ref a p anc) (#v:a) (va:a) (#f:perm)
requires pts_to r #f v ** anchored r va
ensures pts_to r #f v ** anchored r va ** pure (anc va v)

ghost
fn dup_snapshot (#a:Type) (#p:_) (#anc:anchor_rel p) (r : ref a p anc) (#v:a)
requires snapshot r v
ensures snapshot r v ** snapshot r v

ghost
fn take_snapshot (#a:Type) (#p:_) (#f:perm) (#anc:anchor_rel p) (r : ref a p anc) (#v:a)
requires pts_to r #f v
ensures pts_to r #f v ** snapshot r v

ghost
fn take_snapshot_full (#a:Type) (#p:_) (#f:perm) (#anc:anchor_rel p) (r : ref a p anc) (#v:a)
requires pts_to_full r #f v
ensures pts_to_full r #f v ** snapshot r v

ghost
fn recall_snapshot (#a:Type) (#p:_) (#anc:anchor_rel p) (r : ref a p anc) #f (#v0 #v:a)
requires pts_to r #f v ** snapshot r v0
ensures pts_to r #f v ** snapshot r v0 ** pure (p v0 v /\ True)
