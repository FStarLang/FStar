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
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.CancellableInvariant

module U32 = FStar.UInt32
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module CInv = Pulse.Lib.CancellableInvariant

let lock_inv_aux (r:B.box U32.t) (gr:GR.ref U32.t) (v:slprop) : slprop  =
  exists* i p. pts_to r #1.0R i **
               pts_to gr #p i **
               (if i = 0ul then v else emp) **
               pure ((i == 0ul ==> p == 1.0R) /\
                     (i =!= 0ul ==> p == 0.5R)) 

instance is_send_if (i: U32.t) (v: slprop) {| inst: is_send v |} : is_send (if i = 0ul then v else emp) =
  if i = 0ul then inst else is_send_placeless emp

instance is_send_lock_inv_aux r gr v {| is_send v |} : is_send (lock_inv_aux r gr v) =
  Tactics.Typeclasses.solve

let lock_inv (r:B.box U32.t) (gr:GR.ref U32.t) (v:slprop) : slprop =
  lock_inv_aux r gr v

[@@CAbstractStruct]
noeq
type lock = {
  r : B.box U32.t;
  gr : GR.ref U32.t;
  i : cinv;
}

let is_send_tag v (inst: is_send v) = emp

let lock_alive l #p v =
  inv (iname_of l.i) (cinv_vp l.i (lock_inv l.r l.gr v)) ** active l.i p

instance is_send_lock_alive = Tactics.Typeclasses.solve

let lock_acquired l = pts_to l.gr #0.5R 1ul


fn new_lock (v:slprop)
  requires v
  returns l:lock
  ensures lock_alive l v
{
  let gr = GR.alloc 0ul;
  rewrite v as (if 0ul = 0ul then v else emp);
  let r = B.alloc 0ul;
  fold (lock_inv_aux r gr v);
  fold (lock_inv r gr v);
  let i = new_cancellable_invariant (lock_inv r gr v);
  let l = { r; gr; i };
  rewrite each r as l.r;
  rewrite each gr as l.gr;
  rewrite each i as l.i;
  fold (lock_alive l #1.0R v);
  l
}

fn rec acquire (#v:slprop) (#p:perm) (l:lock)
  preserves lock_alive l #p v
  ensures v ** lock_acquired l
{
  unfold (lock_alive l #p v);
  let b =
    with_invariants bool emp_inames (CInv.iname_of l.i) (cinv_vp l.i (lock_inv l.r l.gr v))
        (active l.i p)
        (fun b ->
          active l.i p **
          (cond b (v ** pts_to l.gr #0.5R 1ul) emp))
        fn _ {
      unpack_cinv_vp l.i;
      unfold lock_inv;
      unfold lock_inv_aux;
      with i. assert (pts_to l.r i);
      let b = cas_box l.r 0ul 1ul;
      if b {
        elim_cond_true _ _ _;
        rewrite each i as 0ul;
        GR.(l.gr := 1ul);
        GR.share l.gr;
        fold (lock_inv_aux l.r l.gr v);
        fold (lock_inv l.r l.gr v);
        pack_cinv_vp l.i;
        assert (cinv_vp l.i (lock_inv l.r l.gr v) **
                active l.i p **
                pts_to l.gr #0.5R 1ul **
                v);
        let b = true;
        rewrite (v ** pts_to l.gr #0.5R 1ul)
             as (cond b (v ** pts_to l.gr #0.5R 1ul) emp);
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
                (cond b (v ** pts_to l.gr #0.5R 1ul) emp);
        b
      }
    };

  if b {
    elim_cond_true b _ _;
    fold (lock_alive l #p v);
    fold (lock_acquired l)
  } else {
    elim_cond_false b _ _;
    fold (lock_alive l #p v);
    acquire l
  }
}



fn release (#v:slprop) (#p:perm) (l:lock)
  preserves lock_alive l #p v
  requires lock_acquired l
  requires v
{
  unfold (lock_alive l #p v);

  with_invariants unit emp_inames (CInv.iname_of l.i) (cinv_vp l.i (lock_inv l.r l.gr v))
    (lock_acquired l ** v ** active l.i p)
    (fun _ -> active l.i p)
  fn _ {
    unfold (lock_acquired l);
    unpack_cinv_vp l.i;
    unfold (lock_inv l.r l.gr v);
    unfold (lock_inv_aux l.r l.gr v);
    GR.pts_to_injective_eq l.gr;
    GR.gather l.gr #_ #1ul;
    with i. assert (pts_to l.gr i);
    rewrite each i as 1ul;
    GR.(l.gr := 0ul);
    write_atomic_box l.r 0ul;
    fold (lock_inv_aux l.r l.gr v);
    fold (lock_inv l.r l.gr v);
    pack_cinv_vp l.i;
  };

  fold (lock_alive l #p v)
}



ghost
fn share (#v:slprop) (#p:perm) (l:lock)
  requires lock_alive l #p v
  ensures lock_alive l #(p /. 2.0R) v ** lock_alive l #(p /. 2.0R) v
{
  unfold (lock_alive l #p v);
  CInv.share l.i;
  dup_inv (CInv.iname_of l.i) (cinv_vp l.i (lock_inv l.r l.gr v));  // make this arg implicit
  fold (lock_alive l #(p /. 2.0R) v);
  fold (lock_alive l #(p /. 2.0R) v)
} 



ghost
fn gather (#v:slprop) (#p1 #p2 :perm) (l:lock)
  requires lock_alive l #p1 v
  requires lock_alive l #p2 v
  ensures lock_alive l #(p1 +. p2) v
{
  unfold (lock_alive l #p1 v);
  drop_ (inv (iname_of l.i) _);
  unfold (lock_alive l #p2 v);
  CInv.gather #p1 #p2 l.i;
  fold (lock_alive l #(p1 +. p2) v);
} 


fn free (#v:slprop) (l:lock)
  requires lock_alive l #1.0R v
  requires lock_acquired l
{
  unfold (lock_alive l #1.0R v);
  unfold (lock_acquired l);
  later_credit_buy 1;
  cancel l.i;
  unfold (lock_inv l.r l.gr v);
  unfold (lock_inv_aux l.r l.gr v); with i. _;
  B.free l.r;
  GR.gather l.gr #_ #1ul;
  with v. assert l.gr |-> v; rewrite each v as 1ul; // awkward
  GR.free l.gr;
  ()
}



ghost
fn lock_alive_inj
  (l:lock) (#p1 #p2 :perm) (#v1 #v2 :slprop)
  requires lock_alive l #p1 v1
  requires lock_alive l #p2 v2
  ensures  lock_alive l #p1 v1 ** lock_alive l #p2 v1
{
  unfold (lock_alive l #p2 v2);
  drop_ (inv _ _);
  unfold (lock_alive l #p1 v1);
  dup_inv (CInv.iname_of l.i) (CInv.cinv_vp l.i (lock_inv l.r l.gr v1));
  fold (lock_alive l #p1 v1);
  fold (lock_alive l #p2 v1);
  // TODO: we could also prove from, but that requires a significant amount of congruence lemmas about equiv
  // invariant_name_identifies_invariant (CInv.iname_of l.i) (CInv.iname_of l.i);
}
