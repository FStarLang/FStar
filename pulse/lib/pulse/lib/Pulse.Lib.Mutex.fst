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

module Pulse.Lib.Mutex
#lang-pulse
open Pulse.Lib.Core

open Pulse.Lib.Reference
open Pulse.Lib.SpinLock
open Pulse.Class.PtsTo

module R = Pulse.Lib.Reference
module B = Pulse.Lib.Box

open Pulse.Main

noeq
type mutex (a:Type0) : Type0 = {
  r:B.box a;
  l:lock;
}

let mutex_guard a = R.ref a

let lock_inv (#a:Type0) (r:B.box a) (v:a -> slprop) : slprop =
  exists* x. pts_to r x ** v x

let mutex_live #a m #p v = lock_alive m.l #p (lock_inv m.r v)

let pts_to mg #p x = pts_to mg #p x

let op_Bang #a mg #x #p = R.op_Bang #a mg #x #p
let op_Colon_Equals #a r y #x = R.op_Colon_Equals #a r y #x
let replace #a r y #x = R.replace #a r y #x


fn new_mutex (#a:Type0) (v:a -> slprop) (x:a)
  requires v x
  returns m:mutex a
  ensures mutex_live m v
{
  let r = B.alloc x;
  fold (lock_inv r v);
  let l = new_lock (lock_inv r v);
  let m = {r;l};
  rewrite (lock_alive l (lock_inv r v)) as
          (lock_alive m.l (lock_inv m.r v));
  fold (mutex_live m v);
  m
}


let belongs_to (#a:Type0) (r:mutex_guard a) (m:mutex a) : slprop =
  pure (r == B.box_to_ref m.r /\ R.is_full_ref r) ** lock_acquired m.l


fn lock (#a:Type0) (#v:a -> slprop) (#p:perm) (m:mutex a)
  requires mutex_live m #p v
  returns r:mutex_guard a
  ensures mutex_live m #p v ** r `belongs_to` m ** (exists* x. pts_to r x ** v x)
{
  unfold (mutex_live m#p v);
  acquire m.l;
  unfold lock_inv;
  Box.to_ref_pts_to m.r; Box.to_box_pts_to m.r; // get is_full_ref
  fold (belongs_to (B.box_to_ref m.r) m);
  fold (mutex_live m #p v);
  B.to_ref_pts_to m.r;
  with _x. rewrite (R.pts_to (B.box_to_ref m.r) _x) as
                   (pts_to (B.box_to_ref m.r) _x);
  B.box_to_ref m.r
} 



fn unlock (#a:Type0) (#v:a -> slprop) (#p:perm) (m:mutex a) (mg:mutex_guard a)
  requires mutex_live m #p v ** mg `belongs_to` m ** (exists* x. pts_to mg x ** v x)
  ensures mutex_live m #p v
{
  unfold (mutex_live m #p v);
  unfold (mg `belongs_to` m);
  with x. rewrite (pts_to mg x) as (R.pts_to (B.box_to_ref m.r) x);
  B.to_box_pts_to m.r;
  fold lock_inv;
  release m.l;
  fold (mutex_live m #p v)
}



ghost
fn share (#a:Type0) (#v:a -> slprop) (#p:perm) (m:mutex a)
  requires mutex_live m #p v
  ensures mutex_live m #(p /. 2.0R) v ** mutex_live m #(p /. 2.0R) v
{
  unfold (mutex_live m #p v);
  Pulse.Lib.SpinLock.share m.l;
  fold (mutex_live m #(p /. 2.0R) v);
  fold (mutex_live m #(p /. 2.0R) v);
}



ghost
fn gather (#a:Type0) (#v:a -> slprop) (#p1 #p2:perm) (m:mutex a)
  requires mutex_live m #p1 v ** mutex_live m #p2 v
  ensures mutex_live m #(p1 +. p2) v
{
  unfold (mutex_live m #p2 v);
  unfold (mutex_live m #p1 v);
  Pulse.Lib.SpinLock.gather m.l;
  fold (mutex_live m #(p1 +. p2) v)
}

