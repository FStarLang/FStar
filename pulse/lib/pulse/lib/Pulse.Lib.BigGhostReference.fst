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

module Pulse.Lib.BigGhostReference
open Pulse.Lib.Core
open Pulse.Main
open FStar.PCM
open Pulse.Lib.PCM.Fraction
module T = FStar.Tactics
let ref (a:Type u#2) = ghost_pcm_ref #(fractional a) (pcm_frac #a)

instance non_informative_gref (a:Type u#2) : NonInformative.non_informative (ref a) = {
  reveal = (fun x -> reveal x) <: NonInformative.revealer (ref a);
}

let pts_to (#a:Type) (r:ref a) (#[T.exact (`full_perm)] p:perm) (n:a)
= big_ghost_pcm_pts_to r (Some (n, p)) ** pure (perm_ok p)

```pulse
ghost
fn full_values_compatible (#a:Type u#2) (x:a)
requires emp
ensures pure (compatible pcm_frac (Some (x, full_perm)) (Some (x, full_perm)))
{
   assert pure (FStar.PCM.composable pcm_frac (Some(x, full_perm)) None);
}
```

```pulse
ghost
fn alloc' (#a:Type u#2) (x:a)
requires emp
returns r:ref a
ensures pts_to r x
{
  full_values_compatible x;
  let r = Pulse.Lib.Core.big_ghost_alloc #_ #(pcm_frac #a) (Some (x, full_perm));
  fold (pts_to r #full_perm x);
  r
}
```
let alloc = alloc'

let read_compat (#a:Type u#2) (x:fractional a)
                (v:fractional a { compatible pcm_frac x v })
  : GTot (y:fractional a { compatible pcm_frac y v /\
                           FStar.PCM.frame_compatible pcm_frac x v y })
  = x

```pulse
ghost
fn read' (#a:Type u#2) (r:ref a) (#n:erased a) (#p:perm)
requires pts_to r #p n
returns x:erased a
ensures pts_to r #p n ** pure (n == x)
{
  unfold pts_to r #p n;
  with w. assert (big_ghost_pcm_pts_to r w);
  let x = Pulse.Lib.Core.big_ghost_read r w (fun _ -> w);
  assert pure (compatible pcm_frac w x);
  assert (big_ghost_pcm_pts_to r w);
  fold (pts_to r #p n);
  hide (fst (Some?.v x))
}
```
let read = read'
let ( ! ) #a = read #a

```pulse
ghost
fn write' (#a:Type u#2) (r:ref a) (x:erased a) (#n:erased a)
requires pts_to r #full_perm n
ensures pts_to r #full_perm x
{
  unfold pts_to r #full_perm n;
  with w. assert (big_ghost_pcm_pts_to r w);
  Pulse.Lib.Core.big_ghost_write r _ _ (mk_frame_preserving_upd n x);
  fold pts_to r #full_perm x;
}
```
let ( := ) #a = write' #a

```pulse
ghost
fn free' (#a:Type u#2) (r:ref a) (#n:erased a)
requires pts_to r #full_perm n
ensures emp
{
  unfold pts_to r #full_perm n;
  Pulse.Lib.Core.big_ghost_write r _ _ (mk_frame_preserving_upd_none n);
  Pulse.Lib.Core.drop_ _;
}
```
let free = free'
   
```pulse
ghost
fn share' #a (r:ref a) (#v:erased a) (#p:perm)
requires pts_to r #p v
ensures pts_to r #(half_perm p) v ** pts_to r #(half_perm p) v
{
  unfold pts_to r #p v;
  rewrite big_ghost_pcm_pts_to r (Some (reveal v, p))
      as  big_ghost_pcm_pts_to r (Some (reveal v, half_perm p) `op pcm_frac` Some(reveal v, half_perm p));
  Pulse.Lib.Core.big_ghost_share r (Some (reveal v, half_perm p)) _; //writing an underscore for the first arg also causes a crash
  fold (pts_to r #(half_perm p) v);
  fold (pts_to r #(half_perm p) v);
}
```
let share = share'

```pulse
ghost
fn gather' #a (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
requires pts_to r #p0 x0 ** pts_to r #p1 x1
ensures pts_to r #(sum_perm p0 p1) x0 ** pure (x0 == x1)
{ 
  unfold pts_to r #p0 x0;
  unfold pts_to r #p1 x1;
  Pulse.Lib.Core.big_ghost_gather r (Some (reveal x0, p0)) (Some (reveal x1, p1));
  fold (pts_to r #(sum_perm p0 p1) x0)
}
```
let gather = gather'

let share2 (#a:Type) (r:ref a) (#v:erased a) = share r #v #full_perm
let gather2 (#a:Type) (r:ref a) (#x0 #x1:erased a) = gather r #x0 #x1 #one_half #one_half
         
```pulse
ghost
fn pts_to_injective_eq'
    (#a:Type)
    (#p0 #p1:perm)
    (#v0 #v1:a)
    (r:ref a)
requires pts_to r #p0 v0 ** pts_to r #p1 v1
ensures pts_to r #p0 v0 ** pts_to r #p1 v1 ** pure (v0 == v1)
{
  unfold pts_to r #p0 v0;
  unfold pts_to r #p1 v1;
  Pulse.Lib.Core.big_ghost_gather r (Some (v0, p0)) (Some (v1, p1));
  Pulse.Lib.Core.big_ghost_share r (Some (v0, p0)) (Some (v1, p1));
  fold pts_to r #p0 v0;
  fold pts_to r #p1 v1;
}
```
let pts_to_injective_eq = pts_to_injective_eq'

```pulse
ghost
fn pts_to_perm_bound' (#a:_) (#p:_) (r:ref a) (#v:a)
requires pts_to r #p v
ensures pts_to r #p v ** pure (p `lesser_equal_perm` full_perm)
{
  unfold pts_to r #p v;
  fold pts_to r #p v;
}
```
let pts_to_perm_bound = pts_to_perm_bound'