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

module Pulse.Lib.SpinLock

open Pulse.Lib.Pervasives
open Pulse.Lib.CancellableInvariant

module U32 = FStar.UInt32
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module CInv = Pulse.Lib.CancellableInvariant

let lock_inv_aux (r:B.box U32.t) (gr:GR.ref U32.t) (v:slprop) : (w:slprop { is_storable v ==> is_storable w })  =
  exists* i p. B.pts_to r #1.0R i **
               GR.pts_to gr #p i **
               (if i = 0ul then v else emp) **
               pure ((i == 0ul ==> p == 1.0R) /\
                     (i =!= 0ul ==> p == 0.5R)) 

let lock_inv (r:B.box U32.t) (gr:GR.ref U32.t) (v:slprop) : slprop =
  lock_inv_aux r gr v

let is_storable_lock_inv (r:B.box U32.t) (gr:GR.ref U32.t) (v:slprop)
  : Lemma (is_storable v ==> is_storable (lock_inv r gr v)) = ()

noeq
type lock = {
  r : B.box U32.t;
  gr : GR.ref U32.t;
  i : cinv;
}

let lock_alive l #p v =
  inv (iref_of l.i) (cinv_vp l.i (lock_inv l.r l.gr v)) ** active l.i p

let lock_acquired l = GR.pts_to l.gr #0.5R 1ul

```pulse
fn new_lock (v:slprop { is_storable v })
  requires v
  returns l:lock
  ensures lock_alive l v
{
  let r = B.alloc 0ul;
  let gr = GR.alloc 0ul;
  rewrite v as (if 0ul = 0ul then v else emp);
  fold (lock_inv_aux r gr v);
  fold (lock_inv r gr v);
  is_storable_lock_inv r gr v;
  let i = new_cancellable_invariant (lock_inv r gr v);
  let l = { r; gr; i };
  rewrite each r as l.r;
  rewrite each gr as l.gr;
  rewrite each i as l.i;
  fold (lock_alive l #1.0R v);
  l
}
```

```pulse
fn rec acquire (#v:slprop) (#p:perm) (l:lock)
  requires lock_alive l #p v
  ensures v **  lock_alive l #p v ** lock_acquired l
{
  unfold (lock_alive l #p v);
  let b =
    with_invariants (CInv.iref_of l.i)
      returns b:bool
      ensures inv (CInv.iref_of l.i) (cinv_vp l.i (lock_inv l.r l.gr v)) **
              active l.i p **
              (if b then v ** GR.pts_to l.gr #0.5R 1ul else emp) {
      unpack_cinv_vp l.i;
      unfold lock_inv;
      unfold lock_inv_aux;
      with i. assert (B.pts_to l.r i);
      let b = cas_box l.r 0ul 1ul;
      if b {
        elim_cond_true _ _ _;
        rewrite each i as 0ul;
        GR.(l.gr := 1ul);
        GR.share2 l.gr;
        fold (lock_inv_aux l.r l.gr v);
        fold (lock_inv l.r l.gr v);
        pack_cinv_vp l.i;
        assert (cinv_vp l.i (lock_inv l.r l.gr v) **
                active l.i p **
                GR.pts_to l.gr #0.5R 1ul **
                v);
        let b = true;
        rewrite (v ** GR.pts_to l.gr #0.5R 1ul)
             as (if b then v ** GR.pts_to l.gr #0.5R 1ul else emp);
        b
      } else {
        elim_cond_false _ _ _;
        fold (lock_inv_aux l.r l.gr v);
        fold (lock_inv l.r l.gr v);
        pack_cinv_vp l.i;
        assert (cinv_vp l.i (lock_inv l.r l.gr v) **
                active l.i p);
        let b = false;
        rewrite emp as
                (if b then v ** GR.pts_to l.gr #0.5R 1ul else emp);
        b
      }
    };

  if b {
    rewrite (if b then v ** GR.pts_to l.gr #0.5R 1ul else emp) as
            (v ** GR.pts_to l.gr #0.5R 1ul);
    fold (lock_alive l #p v);
    fold (lock_acquired l)
  } else {
    rewrite (if b then v ** GR.pts_to l.gr #0.5R 1ul else emp) as
            emp;
    fold (lock_alive l #p v);
    acquire l
  }
}
```

```pulse
fn release (#v:slprop) (#p:perm) (l:lock)
  requires lock_alive l #p v ** lock_acquired l ** v
  ensures lock_alive l #p v
{
  unfold (lock_alive l #p v);
  unfold (lock_acquired l);

  with_invariants (CInv.iref_of l.i)
    returns _:unit
    ensures inv (CInv.iref_of l.i) (cinv_vp l.i (lock_inv l.r l.gr v)) **
            active l.i p {
    unpack_cinv_vp l.i;
    unfold (lock_inv l.r l.gr v);
    unfold (lock_inv_aux l.r l.gr v);
    GR.pts_to_injective_eq l.gr;
    GR.gather2 l.gr;
    rewrite (if (1ul = 0ul) then v else emp) as emp;
    write_atomic_box l.r 0ul;
    GR.(l.gr := 0ul);
    fold (lock_inv_aux l.r l.gr v);
    fold (lock_inv l.r l.gr v);
    pack_cinv_vp l.i;
  };

  fold (lock_alive l #p v)
}
```

```pulse
ghost
fn share (#v:slprop) (#p:perm) (l:lock)
  requires lock_alive l #p v
  ensures lock_alive l #(p /. 2.0R) v ** lock_alive l #(p /. 2.0R) v
{
  unfold (lock_alive l #p v);
  CInv.share l.i;
  dup_inv (CInv.iref_of l.i) (cinv_vp l.i (lock_inv l.r l.gr v));  // make this arg implicit
  fold (lock_alive l #(p /. 2.0R) v);
  fold (lock_alive l #(p /. 2.0R) v)
} 
```

let share2 #v l = share #v #1.0R l

```pulse
ghost
fn gather (#v:slprop) (#p1 #p2 :perm) (l:lock)
  requires lock_alive l #p1 v ** lock_alive l #p2 v
  ensures lock_alive l #(p1 +. p2) v
{
  unfold (lock_alive l #p1 v);
  unfold (lock_alive l #p2 v);
  CInv.gather #p1 #p2 l.i;
  fold (lock_alive l #(p1 +. p2) v);
  drop_ (inv _ _)
} 
```

let gather2 #v l = gather #v #0.5R #0.5R l

```pulse
fn free (#v:slprop) (l:lock)
  requires lock_alive l #1.0R v ** lock_acquired l
  ensures emp
{
  unfold (lock_alive l #1.0R v);
  unfold (lock_acquired l);
  cancel l.i;
  unfold (lock_inv l.r l.gr v);
  unfold (lock_inv_aux l.r l.gr v);
  B.free l.r;
  GR.gather l.gr;
  GR.free l.gr;
  rewrite (if (1ul = 0ul) then v else emp) as emp
}
```

```pulse
ghost
fn lock_alive_inj
  (l:lock) (#p1 #p2 :perm) (#v1 #v2 :slprop)
  requires lock_alive l #p1 v1 ** lock_alive l #p2 v2
  ensures  lock_alive l #p1 v1 ** lock_alive l #p2 v1
{
  unfold (lock_alive l #p1 v1);
  unfold (lock_alive l #p2 v2);
  invariant_name_identifies_invariant
    (CInv.iref_of l.i) (CInv.iref_of l.i);
  assert (
    pure (
      cinv_vp l.i (lock_inv l.r l.gr v1)
      ==
      cinv_vp l.i (lock_inv l.r l.gr v2)
    )
  );
  fold (lock_alive l #p1 v1);
  fold (lock_alive l #p2 v1);
}
```

let iref_of l = CInv.iref_of l.i
let iref_v_of l v = cinv_vp l.i (lock_inv l.r l.gr v)
let lock_active #p l = active l.i p

```pulse
ghost
fn share_lock_active (#p:perm) (l:lock)
  requires lock_active #p l
  ensures lock_active #(p /. 2.0R) l ** lock_active #(p /. 2.0R) l
{
  unfold (lock_active #p l);
  CInv.share l.i;
  fold (lock_active #(p /. 2.0R) l);
  fold (lock_active #(p /. 2.0R) l)
}
```

```pulse
ghost
fn gather_lock_active (#p1 #p2:perm) (l:lock)
  requires lock_active #p1 l ** lock_active #p2 l
  ensures lock_active #(p1 +. p2) l
{
  unfold (lock_active #p1 l);
  unfold (lock_active #p2 l);
  CInv.gather #p1 #p2 l.i;
  fold (lock_active #(p1 +. p2) l)
}
```

```pulse
ghost
fn elim_inv_and_active_into_alive (l:lock) (v:slprop) (#p:perm)
  requires emp
  ensures (inv (iref_of l) (iref_v_of l v) ** lock_active #p l) @==> lock_alive l #p v
{
  ghost
  fn aux ()
    requires emp ** (inv (iref_of l) (iref_v_of l v) ** lock_active #p l)
    ensures lock_alive l #p v
  {
    rewrite each
      iref_of l as CInv.iref_of l.i,
      iref_v_of l v as cinv_vp l.i (lock_inv l.r l.gr v);
    unfold (lock_active #p l);
    fold (lock_alive l #p v)
  };

  intro_stick _ _ _ aux
}
```

```pulse
ghost
fn elim_alive_into_inv_and_active (l:lock) (v:slprop) (#p:perm)
  requires emp
  ensures lock_alive l #p v @==> (inv (iref_of l) (iref_v_of l v) ** lock_active #p l)
{
  ghost
  fn aux ()
    requires emp ** lock_alive l #p v
    ensures inv (iref_of l) (iref_v_of l v) ** lock_active #p l
  {
    unfold (lock_alive l #p v);
    fold (lock_active #p l);
    rewrite each
      CInv.iref_of l.i as iref_of l,
      cinv_vp l.i (lock_inv l.r l.gr v) as iref_v_of l v
  };
  intro_stick _ _ _ aux
}
```
