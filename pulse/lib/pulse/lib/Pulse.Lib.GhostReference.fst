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

module Pulse.Lib.GhostReference
#lang-pulse
open Pulse.Lib.Core
open Pulse.Main
open FStar.PCM
open Pulse.Lib.PCM.Fraction
module GR = Pulse.Lib.GhostPCMReference
module T = FStar.Tactics
let ref a = GR.ghost_pcm_ref #_ (pcm_frac #a)

let null #a = GR.null_core_ghost_pcm_ref

let pts_to (#a:Type) (r:ref a) (#[T.exact (`1.0R)] p:perm) (n:a)
= GR.pts_to r (Some (n, p)) ** pure (perm_ok p)

let pts_to_placeless r p n = Tactics.Typeclasses.solve
let pts_to_timeless _ _ _ = ()


ghost
fn full_values_compatible u#a (#a:Type u#a) (x:a)
  ensures pure (compatible pcm_frac (Some (x, 1.0R)) (Some (x, 1.0R)))
{
   assert pure (FStar.PCM.composable pcm_frac (Some(x, 1.0R)) None);
}


ghost
fn alloc u#a (#a:Type u#a) {| small_type u#a |} (x:a)
  returns  r : ref a
  ensures  r |-> x
{
  full_values_compatible x;
  let r = GR.alloc #_ #(pcm_frac #a) (Some (x, 1.0R));
  fold (pts_to r #1.0R x);
  r
}


ghost
fn read u#a (#a:Type u#a) (r:ref a) (#n:erased a) (#p:perm)
  preserves r |-> Frac p n
  returns  x : erased a
  ensures  rewrites_to x n
{
  unfold pts_to r #p n;
  with w. assert (GR.pts_to r w);
  let x = GR.read r w (fun _ -> w);
  assert pure (compatible pcm_frac w x);
  assert (GR.pts_to r w);
  fold (pts_to r #p n);
  hide (fst (Some?.v x))
}


let ( ! ) #a = read #a


ghost
fn ( := ) u#a (#a:Type u#a) (r:ref a) (x:erased a) (#n:erased a)
  requires r |-> n
  ensures  r |-> x
{
  unfold pts_to r #1.0R n;
  with w. assert (GR.pts_to r w);
  GR.write r _ _ (mk_frame_preserving_upd n x);
  fold pts_to r #1.0R x;
}

let write = ( := )


ghost
fn free u#a (#a:Type u#a) (r:ref a) (#n:erased a)
  requires pts_to r n
{
  unfold pts_to r #1.0R n;
  GR.write r _ _ (mk_frame_preserving_upd_none n);
  drop_ (GR.pts_to r _);
}

   

ghost
fn share u#a (#a:Type u#a) (r:ref a) (#v:erased a) (#p:perm)
  requires r |-> Frac p v
  ensures  (r |-> Frac (p /. 2.0R) v) **
           (r |-> Frac (p /. 2.0R) v)
{
  unfold pts_to r #p v;
  GR.share r (Some (reveal v, p /. 2.0R)) (Some (reveal v, p /. 2.0R));
  fold (pts_to r #(p /. 2.0R) v);
  fold (pts_to r #(p /. 2.0R) v);
}


[@@allow_ambiguous]
ghost
fn gather u#a (#a:Type u#a) (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  requires (r |-> Frac p0 x0)
  requires (r |-> Frac p1 x1)
  ensures (r |-> Frac (p0 +. p1) x0)
  ensures pure (x0 == x1)
{ 
  unfold pts_to r #p0 x0;
  unfold pts_to r #p1 x1;
  GR.gather r (Some (reveal x0, p0)) (Some (reveal x1, p1));
  fold (pts_to r #(p0 +. p1) x0)
}


[@@allow_ambiguous]
ghost
fn pts_to_injective_eq  u#a (#a:Type u#a)
                        (#p #q:_)
                        (#v0 #v1:a)
                        (r:ref a)
  requires (r |-> Frac p v0)
  requires (r |-> Frac q v1)
  ensures (r |-> Frac p v0)
  ensures (r |-> Frac q v1)
  ensures pure (v0 == v1)
{
  unfold pts_to r #p v0;
  unfold pts_to r #q v1;
  GR.gather r (Some (v0, p)) (Some (v1, q));
  GR.share r (Some (v0, p)) (Some (v1, q));
  fold pts_to r #p v0;
  fold pts_to r #q v1;
}



ghost
fn pts_to_perm_bound u#a (#a:Type u#a) (#p:_) (r:ref a) (#v:a)
  requires r |-> Frac p v
  ensures (r |-> Frac p v)
  ensures pure (p <=. 1.0R)
{
  unfold pts_to r #p v;
  fold pts_to r #p v;
}


ghost
fn pts_to_not_null u#a (#a:Type u#a) (#p:_) (r:ref a) (#v:a)
  preserves r |-> Frac p v
  ensures  pure (r =!= null)
{
  unfold pts_to r #p v;
  GR.pts_to_not_null r _;
  fold pts_to r #p v;
}