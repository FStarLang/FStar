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


module Box = Pulse.Lib.Box
module U32 = FStar.UInt32
module GR = Pulse.Lib.GhostReference

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

let lock_inv_aux (r:ref U32.t) (gr:GR.ref U32.t) (v:vprop) : (w:vprop { is_big v ==> is_big w })  =
  exists* i p. pts_to r #full_perm i **
               GR.pts_to gr #p i **
               (if i = 0ul then v else emp) **
               pure ((i == 0ul ==> p == full_perm) /\
                     (i =!= 0ul ==> p == half_perm full_perm)) 

let lock_inv (r:ref U32.t) (gr:GR.ref U32.t) (v:vprop) : vprop =
  lock_inv_aux r gr v

let is_big_lock_inv (r:ref U32.t) (gr:GR.ref U32.t) (v:vprop)
  : Lemma (is_big v ==> is_big (lock_inv r gr v)) = ()

noeq
type lock = {
  r : ref U32.t;
  gr : GR.ref U32.t;
  i : cinv;
}

let lock_alive l #p v =
  inv l.i.i (cancellable l.i.t (lock_inv l.r l.gr v)) ** active p l.i.t

let lock_acquired l #p v =
  inv l.i.i (cancellable l.i.t (lock_inv l.r l.gr v)) ** active p l.i.t ** GR.pts_to l.gr #(half_perm full_perm) 1ul

```pulse
fn new_lock_aux (v:vprop { is_big v })
  requires v
  returns l:lock
  ensures lock_alive l v
{
  let r = alloc 0ul;
  let gr = GR.alloc 0ul;
  rewrite v as (if 0ul = 0ul then v else emp);
  fold (lock_inv_aux r gr v);
  fold (lock_inv r gr v);
  is_big_lock_inv r gr v;
  let i = new_cancellable_invariant (lock_inv r gr v);
  let l = { r; gr; i };
  rewrite each r as l.r;
  rewrite each gr as l.gr;
  rewrite each i as l.i;
  fold (lock_alive l #full_perm v);
  l
}
```

let new_lock = new_lock_aux

```pulse
fn rec acquire_aux (#v:vprop) (#p:perm) (l:lock)
  requires lock_alive l #p v
  ensures v **  lock_acquired l #p v
{
  unfold (lock_alive l #p v);
  let b =
    with_invariants l.i.i
      returns b:bool
      ensures active p l.i.t **
              (if b then v ** GR.pts_to l.gr #(half_perm full_perm) 1ul else emp) {
      take l.i.t;
      unfold lock_inv;
      unfold lock_inv_aux;
      let b = cas l.r 0ul 1ul;
      if b {
        elim_cond_true _ _ _;
        GR.(l.gr := 1ul);
        GR.share2 l.gr;
        rewrite emp as (if (1ul = 0ul) then v else emp);
        fold (lock_inv_aux l.r l.gr v);
        fold (lock_inv l.r l.gr v);
        give l.i.t;
        assert (cancellable l.i.t (lock_inv l.r l.gr v) **
                active p l.i.t **
                GR.pts_to l.gr #(half_perm full_perm) 1ul **
                v);
        let b = true;
        rewrite (v ** GR.pts_to l.gr #(half_perm full_perm) 1ul)
             as (if b then v ** GR.pts_to l.gr #(half_perm full_perm) 1ul else emp);
        b
      } else {
        elim_cond_false _ _ _;
        fold (lock_inv_aux l.r l.gr v);
        fold (lock_inv l.r l.gr v);
        give l.i.t;
        assert (cancellable l.i.t (lock_inv l.r l.gr v) **
                active p l.i.t);
        let b = false;
        rewrite emp as
                (if b then v ** GR.pts_to l.gr #(half_perm full_perm) 1ul else emp);
        b
      }
    };

  if b {
    rewrite (if b then v ** GR.pts_to l.gr #(half_perm full_perm) 1ul else emp) as
            (v ** GR.pts_to l.gr #(half_perm full_perm) 1ul);
    fold (lock_acquired l #p v);
  } else {
    rewrite (if b then v ** GR.pts_to l.gr #(half_perm full_perm) 1ul else emp) as
            emp;
    fold (lock_alive l #p v);
    acquire_aux l
  }
}
```

let acquire = acquire_aux

```pulse
fn release_aux (#v:vprop) (#p:perm) (l:lock)
  requires v ** lock_acquired l #p v
  ensures lock_alive l #p v
{
  unfold (lock_acquired l #p v);

  with_invariants l.i.i
    returns _:unit
    ensures active p l.i.t {
    take l.i.t;
    unfold (lock_inv l.r l.gr v);
    unfold (lock_inv_aux l.r l.gr v);
    GR.pts_to_injective_eq l.gr;
    GR.gather2 l.gr;
    rewrite (if (1ul = 0ul) then v else emp) as emp;
    write_atomic l.r 0ul;
    GR.(l.gr := 0ul);
    fold (lock_inv_aux l.r l.gr v);
    fold (lock_inv l.r l.gr v);
    give l.i.t;
  };

  fold (lock_alive l #p v)
}
```

let release = release_aux

```pulse
ghost
fn share_aux (#v:vprop) (#p:perm) (l:lock)
  requires lock_alive l #p v
  ensures lock_alive l #(half_perm p) v ** lock_alive l #(half_perm p) v
  opens emp_inames
{
  unfold (lock_alive l #p v);
  share l.i.t;
  dup_inv l.i.i (cancellable l.i.t (lock_inv l.r l.gr v));  // make this arg implicit
  fold (lock_alive l #(half_perm p) v);
  fold (lock_alive l #(half_perm p) v)
} 
```

let share = share_aux

```pulse
ghost
fn gather_aux (#v:vprop) (#p:perm) (l:lock)
  requires lock_alive l #(half_perm p) v ** lock_alive l #(half_perm p) v
  ensures lock_alive l #p v
  opens emp_inames
{
  unfold (lock_alive l #(half_perm p) v);
  unfold (lock_alive l #(half_perm p) v);
  gather l.i.t;
  fold (lock_alive l #p v);
  drop_ (inv _ _)
} 
```

let gather = gather_aux

```pulse
fn rec free_aux (#v:vprop) (l:lock)
  requires lock_alive l #full_perm v
  ensures v
{
  unfold (lock_alive l #full_perm v);

  let b = with_invariants l.i.i
    returns b:bool
    ensures active full_perm l.i.t **
            (if b then (v ** GR.pts_to l.gr #(half_perm full_perm) 2ul)
                  else emp) {
    take l.i.t;
    unfold (lock_inv l.r l.gr v);
    unfold (lock_inv_aux l.r l.gr v);
    let b = cas l.r 0ul 2ul;
    if b {
      elim_cond_true _ _ _;
      rewrite (if (0ul = 0ul) then v else emp) as v;
      GR.(l.gr := 2ul);
      GR.share l.gr;
      rewrite emp as (if (2ul = 0ul) then v else emp);
      fold (lock_inv_aux l.r l.gr v);
      fold (lock_inv l.r l.gr v);
      give l.i.t;
      let b = true;
      rewrite (v ** GR.pts_to l.gr #(half_perm full_perm) 2ul)
           as (if b then (v ** GR.pts_to l.gr #(half_perm full_perm) 2ul) else emp);
      b
    } else {
      elim_cond_false _ _ _;
      fold (lock_inv_aux l.r l.gr v);
      fold (lock_inv l.r l.gr v);
      give l.i.t;
      let b = false;
      rewrite emp as (if b then (v ** GR.pts_to l.gr #(half_perm full_perm) 2ul) else emp);
      b
    }
  };

  if b {
    rewrite (if b then (v ** GR.pts_to l.gr #(half_perm full_perm) 2ul) else emp) as
            (v ** GR.pts_to l.gr #(half_perm full_perm) 2ul);
    cancel l.i;
    unfold (lock_inv l.r l.gr v);
    unfold (lock_inv_aux l.r l.gr v);
    GR.gather l.gr;
    rewrite (if (2ul = 0ul) then v else emp) as emp;
    free l.r;
    GR.free l.gr
  } else {
    rewrite (if b then (v ** GR.pts_to l.gr #(half_perm full_perm) 2ul) else emp) as
            emp;
    fold (lock_alive l #full_perm v);
    free_aux l
  }
}
```

let free = free_aux
