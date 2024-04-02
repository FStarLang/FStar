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

open Pulse.Lib.Pervasives

module GR = Pulse.Lib.GhostReference

let token = GR.ref bool

let big_star (p q : vprop)
: Lemma
    (requires is_big p /\ is_big q)
    (ensures is_big (p ** q))
    [SMTPat (is_big (p ** q))] = big_star p q

let big_exists (#a:Type u#a) (p: a -> vprop)
: Lemma
    (requires forall x. is_big (p x))
    (ensures is_big (op_exists_Star p))
    [SMTPat (is_big (op_exists_Star p))] = big_exists p

let cancellable_aux (t:token) (v:vprop) : (w:vprop { is_big v ==> is_big w }) =
  exists* (b:bool). GR.pts_to t #(half_perm full_perm) b **
                    (if b then v else emp)

let cancellable t v = cancellable_aux t v

let cancellable_big t v = ()

let active p t = GR.pts_to t #(half_perm p) true

let taken t = GR.pts_to t #(half_perm full_perm) true

```pulse
ghost
fn new_cancellable_invariant_aux (v:vprop { is_big v })
  requires v
  returns r:cinv
  ensures inv r.i (cancellable r.t v) ** active full_perm r.t
  opens emp_inames
{
  let t = GR.alloc true;
  rewrite v as (if true then v else emp);
  GR.share2 t;
  fold (cancellable_aux t v);
  fold (cancellable t v);
  cancellable_big t v;
  let i = new_invariant (cancellable t v);
  fold (active full_perm t);
  let r = E i t;
  rewrite each t as r.t;
  rewrite each i as r.i;
  r
}
```

let new_cancellable_invariant = new_cancellable_invariant_aux

```pulse
ghost
fn take_aux (#p:perm) (#v:vprop) (t:token)
  requires cancellable t v ** active p t
  ensures v ** active p t ** taken t
  opens emp_inames
{
  unfold cancellable;
  unfold cancellable_aux;
  unfold active;
  GR.pts_to_injective_eq t;
  rewrite (if true then v else emp) as v;
  fold (active p t);
  fold (taken t)
}
```

let take = take_aux

```pulse
ghost
fn give_aux (#v:vprop) (t:token)
  requires v ** taken t
  ensures cancellable t v
  opens emp_inames
{
  unfold taken;
  rewrite v as (if true then v else emp);
  fold (cancellable_aux t v);
  fold (cancellable t v)
}
```

let give = give_aux

```pulse
ghost
fn share_aux (#p:perm) (t:token)
  requires active p t
  ensures active (half_perm p) t ** active (half_perm p) t
  opens emp_inames
{
  unfold active;
  GR.share t;
  fold active;
  fold active
}
```

let share = share_aux

```pulse
ghost
fn gather_aux (#p:perm) (t:token)
  requires active (half_perm p) t ** active (half_perm p) t
  ensures active p t
  opens emp_inames
{
  unfold active;
  unfold active;
  GR.gather t;
  with _p _v. rewrite (GR.pts_to t #_p _v) as (GR.pts_to t #(half_perm p) _v);
  fold active;
}
```

let gather = gather_aux


```pulse
ghost
fn cancel_ (#v:vprop) (t:token)
requires cancellable t v **
         active full_perm t
ensures cancellable t v ** v
opens emp_inames
{
  unfold cancellable;
  unfold cancellable_aux;
  unfold active;
  GR.pts_to_injective_eq t;
  rewrite (if true then v else emp) as v;
  GR.gather t;
  GR.(t := false);
  rewrite emp as (if false then v else emp);
  GR.share2 t;
  fold (cancellable_aux t v);
  fold (cancellable t v);
  drop_ (GR.pts_to t #(half_perm full_perm) _)
}
```

```pulse
ghost
fn cancel_aux (#p:perm) (#v:vprop) (i:cinv)
  requires inv i.i (cancellable i.t v) ** active full_perm i.t
  ensures v
  opens (add_inv emp_inames i.i)
{
  with_invariants i.i
    returns _:unit
    ensures v {
    cancel_ i.t  
  };
  drop_ (inv i.i _)
}
```
