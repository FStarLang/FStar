(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at


   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.MutexToken
#lang-pulse

open Pulse.Lib.Pervasives

module T = FStar.Tactics

module R = Pulse.Lib.Reference
module B = Pulse.Lib.Box
module L = Pulse.Lib.SpinLockToken

noeq
type mutex (#a:Type0) (p:a -> slprop) = {
  r : B.box a;
  l : L.lock (exists* v. pts_to r v ** p v)
}

let mutex_guard (a:Type0) : Type0 = R.ref a

let pts_to (#a:Type0) (mg:mutex_guard a) (#[T.exact (`1.0R)] p:perm) (x:a) : slprop =
  pts_to mg #p x

let ( ! ) (#a:Type0) (mg:mutex_guard a) (#x:erased a) (#p:perm)
  : stt a
      (requires pts_to mg #p x)
      (ensures fun y -> pts_to mg #p x ** pure (reveal x == y)) =
  
  R.op_Bang #a mg #x #p

let ( := ) (#a:Type0) (mg:mutex_guard a) (y:a) (#x:erased a)
  : stt unit
      (requires mg `pts_to` x)
      (ensures fun _ -> mg `pts_to` y) =
  
  R.op_Colon_Equals #a mg y #x

let replace (#a:Type0) (mg:mutex_guard a) (y:a) (#x:erased a)
  : stt a
      (requires mg `pts_to` x)
      (ensures fun r -> mg `pts_to` y ** pure (r == reveal x)) =
  
  R.replace #a mg y #x


fn new_mutex (#a:Type0) (v:a -> slprop { forall (x:a). is_storable (v x) }) (x:a)
  requires v x
  returns _:mutex v
  ensures emp
{
  let r = B.alloc x;
  let l = L.new_lock (exists* x. B.pts_to r x ** v x);
  let m = {r; l};
  m
}


let belongs_to (#a:Type0) (#v:a -> slprop) (mg:mutex_guard a) (m:mutex v) : slprop =
  pure (mg == B.box_to_ref m.r) ** L.lock_acquired m.l


fn lock (#a:Type0) (#v:a -> slprop) (m:mutex v)
  requires emp
  returns mg:mutex_guard a
  ensures mg `belongs_to` m ** (exists* x. pts_to mg x ** v x)
{
  L.acquire m.l;
  B.to_ref_pts_to m.r;
  with _x. rewrite (R.pts_to (B.box_to_ref m.r) _x) as
                   (pts_to (B.box_to_ref m.r) _x);
  fold ((B.box_to_ref m.r) `belongs_to` m);
  B.box_to_ref m.r
}



fn unlock (#a:Type0) (#v:a -> slprop) (m:mutex v) (mg:mutex_guard a)
  requires mg `belongs_to` m ** (exists* x. pts_to mg x ** v x)
  ensures emp
{
  unfold (mg `belongs_to` m);
  with x. rewrite (pts_to mg x) as (R.pts_to (B.box_to_ref m.r) x);
  B.to_box_pts_to m.r;
  L.release m.l
}

