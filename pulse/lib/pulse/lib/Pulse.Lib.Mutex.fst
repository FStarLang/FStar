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
open Pulse.Lib.Core

open Pulse.Lib.Reference
open Pulse.Lib.SpinLock

module B = Pulse.Lib.Box

open Pulse.Main

noeq
type mutex (a:Type0) : Type0 = {
  r:B.box a;
  l:lock;
}

let lock_inv (#a:Type0) (r:B.box a) (v:a -> vprop)
  : (w:vprop { (forall x. is_big (v x)) ==> is_big w }) =
  exists* x. B.pts_to r x ** v x

let mutex_live #a m #p v = lock_alive m.l #p (lock_inv m.r v)

```pulse
fn new_mutex' (#a:Type0) (v:a -> vprop { forall x. is_big (v x) }) (x:a)
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
```

let new_mutex = new_mutex'

let belongs_to_mutex (#a:Type0) (r:ref a) (m:mutex a) : vprop =
  pure (r == B.box_to_ref m.r) ** lock_acquired m.l

```pulse
fn lock' (#a:Type0) (#v:a -> vprop) (#p:perm) (m:mutex a)
  requires mutex_live m #p v
  returns r:ref a
  ensures mutex_live m #p v ** r `belongs_to_mutex` m ** (exists* x. pts_to r x ** v x)
{
  unfold (mutex_live m#p v);
  acquire m.l;
  unfold lock_inv;
  fold (belongs_to_mutex (B.box_to_ref m.r) m);
  fold (mutex_live m #p v);
  B.to_ref_pts_to m.r;
  B.box_to_ref m.r
} 
```

let lock = lock'

```pulse
fn unlock' (#a:Type0) (#v:a -> vprop) (#p:perm) (m:mutex a) (r:ref a)
  requires mutex_live m #p v ** r `belongs_to_mutex` m ** (exists* x. pts_to r x ** v x)
  ensures mutex_live m #p v
{
  unfold (mutex_live m #p v);
  unfold (r `belongs_to_mutex` m);
  with x. rewrite (pts_to r x) as (pts_to (B.box_to_ref m.r) x);
  B.to_box_pts_to m.r;
  fold lock_inv;
  release m.l;
  fold (mutex_live m #p v)
}
```

let unlock = unlock'

```pulse
ghost
fn share_aux (#a:Type0) (#v:a -> vprop) (#p:perm) (m:mutex a)
  requires mutex_live m #p v
  ensures mutex_live m #(half_perm p) v ** mutex_live m #(half_perm p) v
{
  unfold (mutex_live m #p v);
  Pulse.Lib.SpinLock.share m.l;
  fold (mutex_live m #(half_perm p) v);
  fold (mutex_live m #(half_perm p) v);
}
```

let share = share_aux

```pulse
ghost
fn gather_aux (#a:Type0) (#v:a -> vprop) (#p:perm) (m:mutex a)
  requires mutex_live m #(half_perm p) v ** mutex_live m #(half_perm p) v
  ensures mutex_live m #p v
{
  unfold (mutex_live m #(half_perm p) v);
  unfold (mutex_live m #(half_perm p) v);
  Pulse.Lib.SpinLock.gather m.l;
  fold (mutex_live m #p v)
}
```

let gather = gather_aux