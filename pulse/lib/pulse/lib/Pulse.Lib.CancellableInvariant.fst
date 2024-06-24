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
#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"
open Pulse.Lib.Pervasives

module GR = Pulse.Lib.GhostReference

noeq
type cinv = {
  i:iref;
  r:GR.ref bool;
}

instance non_informative_cinv = {
  reveal = (fun r -> Ghost.reveal r) <: NonInformative.revealer cinv;
}

let cinv_vp_aux (r:GR.ref bool) (v:vprop) : (w:vprop { is_big v ==> is_big w }) =
  exists* (b:bool). GR.pts_to r #0.5R b **
                    (if b then v else emp)

let cinv_vp c v = cinv_vp_aux c.r v

let is_big_cinv_vp _ _ = ()

let active c p = GR.pts_to c.r #(p /. 2.0R) true

let active_is_small p c = ()

let iref_of c = c.i

```pulse
ghost
fn new_cancellable_invariant (v:vprop { is_big v })
  requires v
  returns c:cinv
  ensures inv (iref_of c) (cinv_vp c v) ** active c 1.0R
  opens emp_inames
{
  let r = GR.alloc true;
  rewrite v as (if true then v else emp);
  GR.share2 r;
  fold (cinv_vp_aux r v);
  let i = new_invariant (cinv_vp_aux r v);
  let c = {i;r};
  rewrite (inv i (cinv_vp_aux r v)) as (inv (iref_of c) (cinv_vp c v));
  with _p _v. rewrite (GR.pts_to r #_p _v) as (active c 1.0R);
  c
}
```

let unpacked c _v = GR.pts_to c.r #0.5R true


```pulse
ghost
fn unpack_cinv_vp (#p:perm) (#v:vprop) (c:cinv)
  requires cinv_vp c v ** active c p
  ensures v ** unpacked c v ** active c p
  opens emp_inames
{
  unfold cinv_vp;
  unfold cinv_vp_aux;
  unfold active;
  GR.pts_to_injective_eq c.r;
  rewrite (if true then v else emp) as v;
  fold (active c p);
  fold (unpacked c v)
}
```

```pulse
ghost
fn pack_cinv_vp (#v:vprop) (c:cinv)
  requires v ** unpacked c v
  ensures cinv_vp c v
  opens emp_inames
{
  unfold unpacked;
  rewrite v as (if true then v else emp);
  fold (cinv_vp_aux c.r v);
  fold (cinv_vp c v)
}
```

```pulse
ghost
fn share (#p:perm) (c:cinv)
  requires active c p
  ensures active c (p /. 2.0R) ** active c (p /. 2.0R)
  opens emp_inames
{
  unfold active;
  GR.share c.r;
  fold active;
  fold active
}
```

let share2 c = share #1.0R c

```pulse
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
```

let gather2 c = gather #0.5R #0.5R c

```pulse
ghost
fn cancel_ (#v:vprop) (c:cinv)
requires cinv_vp c v **
         active c 1.0R
ensures cinv_vp c v ** v
opens emp_inames
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
  drop_ (GR.pts_to c.r #0.5R _)
}
```

```pulse
ghost
fn cancel (#v:vprop) (c:cinv)
  requires inv (iref_of c) (cinv_vp c v) ** active c 1.0R
  ensures v
  opens (add_inv emp_inames (iref_of c))
{
  with_invariants (iref_of c)
    returns _:unit
    ensures inv (iref_of c) (cinv_vp c v) ** v
    opens (add_inv emp_inames (iref_of c)) {
    cancel_ c
  };
  drop_ (inv (iref_of c) _)
}
```
