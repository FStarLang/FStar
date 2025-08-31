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

module Pulse.Lib.HigherGhostReference
#lang-pulse
open Pulse.Lib.Core
open Pulse.Main
open FStar.PCM
open Pulse.Lib.PCM.Fraction
module T = FStar.Tactics
let ref (a:Type u#1) = ghost_pcm_ref #_ (pcm_frac #a)

instance non_informative_gref (a:Type u#1) : NonInformative.non_informative (ref a) = {
  reveal = (fun x -> Ghost.reveal x) <: NonInformative.revealer (ref a);
}

let pts_to (#a:Type) (r:ref a) (#[T.exact (`1.0R)] p:perm) (n:a)
= ghost_pcm_pts_to r (Some (n, p)) ** pure (perm_ok p)

let pts_to_timeless _ _ _ = ()


ghost
fn full_values_compatible (#a:Type u#1) (x:a)
  requires emp
  ensures pure (compatible pcm_frac (Some (x, 1.0R)) (Some (x, 1.0R)))
{
   assert pure (FStar.PCM.composable pcm_frac (Some(x, 1.0R)) None);
}



ghost
fn alloc (#a:Type u#1) (x:a)
  requires emp
  returns r:ref a
  ensures pts_to r x
{
  full_values_compatible x;
  let r = Pulse.Lib.Core.ghost_alloc #_ #(pcm_frac #a) (Some (x, 1.0R));
  fold (pts_to r #1.0R x);
  r
}


let read_compat (#a:Type u#1) (x:fractional a)
                (v:fractional a { compatible pcm_frac x v })
  : GTot (y:fractional a { compatible pcm_frac y v /\
                           FStar.PCM.frame_compatible pcm_frac x v y })
  = x


ghost
fn read (#a:Type u#1) (r:ref a) (#n:erased a) (#p:perm)
  preserves pts_to r #p n
  returns x:erased a
  ensures rewrites_to x n
{
  unfold pts_to r #p n;
  with w. assert (ghost_pcm_pts_to r w);
  let x = Pulse.Lib.Core.ghost_read r w (fun _ -> w);
  assert pure (compatible pcm_frac w x);
  assert (ghost_pcm_pts_to r w);
  fold (pts_to r #p n);
  hide (fst (Some?.v x))
}


let ( ! ) #a = read #a


ghost
fn ( := ) (#a:Type u#1) (r:ref a) (x:erased a) (#n:erased a)
  requires pts_to r #1.0R n
  ensures pts_to r #1.0R x
{
  unfold pts_to r #1.0R n;
  with w. assert (ghost_pcm_pts_to r w);
  Pulse.Lib.Core.ghost_write r _ _ (mk_frame_preserving_upd n x);
  fold pts_to r #1.0R x;
}

let write = ( := )


ghost
fn free #a (r:ref a) (#n:erased a)
  requires pts_to r #1.0R n
  ensures emp
{
  unfold pts_to r #1.0R n;
  Pulse.Lib.Core.ghost_write r _ _ (mk_frame_preserving_upd_none n);
  Pulse.Lib.Core.drop_ (ghost_pcm_pts_to _ _);
}

   

ghost
fn share #a (r:ref a) (#v:erased a) (#p:perm)
  requires pts_to r #p v
  ensures pts_to r #(p /. 2.0R) v ** pts_to r #(p /. 2.0R) v
{
  unfold pts_to r #p v;
  rewrite ghost_pcm_pts_to r (Some (reveal v, p))
      as  ghost_pcm_pts_to r (Some (reveal v, p /. 2.0R) `op pcm_frac` Some(reveal v, p /. 2.0R));
  Pulse.Lib.Core.ghost_share r (Some (reveal v, p /. 2.0R)) _; //writing an underscore for the first arg also causes a crash
  fold (pts_to r #(p /. 2.0R) v);
  fold (pts_to r #(p /. 2.0R) v);
}



ghost
fn gather #a (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  requires pts_to r #p0 x0 ** pts_to r #p1 x1
  ensures pts_to r #(p0 +. p1) x0 ** pure (x0 == x1)
{ 
  unfold pts_to r #p0 x0;
  unfold pts_to r #p1 x1;
  Pulse.Lib.Core.ghost_gather r (Some (reveal x0, p0)) (Some (reveal x1, p1));
  fold (pts_to r #(p0 +. p1) x0)
}


ghost
fn pts_to_injective_eq
    (#a:Type)
    (#p0 #p1:perm)
    (#v0 #v1:a)
    (r:ref a)
  requires pts_to r #p0 v0 ** pts_to r #p1 v1
  ensures pts_to r #p0 v0 ** pts_to r #p1 v1 ** pure (v0 == v1)
{
  unfold pts_to r #p0 v0;
  unfold pts_to r #p1 v1;
  Pulse.Lib.Core.ghost_gather r (Some (v0, p0)) (Some (v1, p1));
  Pulse.Lib.Core.ghost_share r (Some (v0, p0)) (Some (v1, p1));
  fold pts_to r #p0 v0;
  fold pts_to r #p1 v1;
}



ghost
fn pts_to_perm_bound (#a:_) (#p:_) (r:ref a) (#v:a)
  requires pts_to r #p v
  ensures pts_to r #p v ** pure (p <=. 1.0R)
{
  unfold pts_to r #p v;
  fold pts_to r #p v;
}

