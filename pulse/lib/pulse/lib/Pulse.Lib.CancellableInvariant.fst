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

module Pulse.Lib.CancellableInvariant
#lang-pulse
open Pulse.Lib.Pervasives

module GR = Pulse.Lib.GhostReference

noeq
type cinv = {
  i:iname;
  r:GR.ref bool;
}

instance non_informative_cinv = {
  reveal = (fun r -> Ghost.reveal r) <: NonInformative.revealer cinv;
}

let cinv_vp_aux (r:GR.ref bool) (v:slprop) : (w:slprop { is_storable v ==> is_storable w }) =
  exists* (b:bool). pts_to r #0.5R b **
                    (if b then v else emp)

let cinv_vp c v = cinv_vp_aux c.r v

let is_storable_cinv_vp _ _ = ()

let active c p = pts_to c.r #(p /. 2.0R) true

let active_is_slprop2 p c = ()

let iname_of c = c.i


ghost
fn new_cancellable_invariant (v:slprop { is_storable v })
  requires v
  returns c:cinv
  ensures inv (iname_of c) (cinv_vp c v) ** active c 1.0R
  opens []
{
  let r = GR.alloc true;
  rewrite v as (if true then v else emp);
  GR.share2 r;
  fold (cinv_vp_aux r v);
  let i = new_invariant (cinv_vp_aux r v);
  let c = {i;r};
  rewrite (inv i (cinv_vp_aux r v)) as (inv (iname_of c) (cinv_vp c v));
  with _p _v. rewrite (pts_to r #_p _v) as (active c 1.0R);
  c
}


let unpacked c _v = pts_to c.r #0.5R true



ghost
fn unpack_cinv_vp (#p:perm) (#v:slprop) (c:cinv)
  requires cinv_vp c v ** active c p
  ensures v ** unpacked c v ** active c p
  opens []
{
  unfold cinv_vp;
  unfold cinv_vp_aux;
  unfold active;
  GR.pts_to_injective_eq c.r;
  rewrite (if true then v else emp) as v;
  fold (active c p);
  fold (unpacked c v)
}



ghost
fn pack_cinv_vp (#v:slprop) (c:cinv)
  requires v ** unpacked c v
  ensures cinv_vp c v
  opens []
{
  unfold unpacked;
  rewrite v as (if true then v else emp);
  fold (cinv_vp_aux c.r v);
  fold (cinv_vp c v)
}



ghost
fn share (#p:perm) (c:cinv)
  requires active c p
  ensures active c (p /. 2.0R) ** active c (p /. 2.0R)
  opens []
{
  unfold active;
  GR.share c.r;
  fold active;
  fold active
}


let share2 c = share #1.0R c


ghost
fn gather (#p1 #p2:perm) (c:cinv)
  requires active c p1 ** active c p2
  ensures active c (p1 +. p2)
{
  unfold (active c p1);
  unfold (active c p2);
  GR.gather c.r #_ #_ #(p1 /. 2.0R) #(p2 /. 2.0R);
  fold active c (p1 +. p2);
}


let gather2 c = gather #0.5R #0.5R c


ghost
fn cancel_ (#v:slprop) (c:cinv)
requires cinv_vp c v **
         active c 1.0R
ensures cinv_vp c v ** v
opens []
{
  unfold cinv_vp;
  unfold cinv_vp_aux;
  unfold active;
  GR.pts_to_injective_eq c.r;
  rewrite (if true then v else emp) as v;
  GR.gather c.r;
  GR.(c.r := false);
  rewrite emp as (if false then v else emp);
  GR.share2 c.r;
  fold (cinv_vp_aux c.r v);
  fold (cinv_vp c v);
  drop_ (pts_to c.r #0.5R _)
}



ghost
fn cancel (#v:storable) (c:cinv)
  requires inv (iname_of c) (cinv_vp c v) ** active c 1.0R
  ensures v
  opens [iname_of c]
{
  with_invariants (iname_of c)
    returns _:unit
    ensures later (cinv_vp c v) ** v
    opens [iname_of c] {
    is_storable_cinv_vp c v;
    later_elim_storable _;
    cancel_ c;
    later_intro (cinv_vp c v);
  };
  drop_ (inv (iname_of c) _)
}

