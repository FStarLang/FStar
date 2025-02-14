module PulseTutorialSolutions.SpinLock3
#lang-pulse
open Pulse.Lib.Pervasives
module Box = Pulse.Lib.Box
module U32 = FStar.UInt32
module GR = Pulse.Lib.GhostReference

//lock$
let maybe ([@@@equate_by_smt] b:bool) (p:slprop) =
    if b then p else emp

let core_lock_inv (r:Box.box U32.t) (p:slprop) = 
  exists* v.
      Box.pts_to r v **
      maybe (v = 0ul) p

let lock_inv (r:Box.box U32.t) (live:GR.ref bool) (p:slprop) =
  exists* b. 
    GR.pts_to live #one_half b **
    maybe b (core_lock_inv r p)

noeq
type lock (p:slprop) = {
  r:Box.box U32.t;
  live:GR.ref bool;
  i:inv (lock_inv r live p);
}

let lock_live #p (l:lock p) (#[default_arg (`full_perm)] perm:perm) =
    GR.pts_to l.live #(half_perm perm) true
//lock$


fn new_lock ()
requires p
returns l:lock p
ensures lock_live l
{
  let r = Box.alloc 0ul;
  let live = GR.alloc true;
  GR.share live;
  fold (maybe true p);
  fold (core_lock_inv r p);
  fold (maybe true (core_lock_inv r p));
  fold (lock_inv r live p);
  let i = new_invariant (lock_inv r live p);
  let l = { r; live; i};
  rewrite each live as l.live;
  fold (lock_live l #full_perm);
  l
}




fn free_lock #p (l:lock p)
requires lock_live l 
ensures emp
{
  with_invariants l.i 
  returns _:unit
  ensures core_lock_inv l.r p
  {
    unfold lock_inv;
    with _b. _;
    unfold (lock_live l #full_perm);
    GR.gather l.live;
    GR.write l.live false;
    GR.share l.live;
    fold (maybe false (core_lock_inv l.r p));
    fold (lock_inv l.r l.live p);
    drop_ (GR.pts_to l.live #one_half false);
    rewrite each _b as true;
    unfold (maybe true (core_lock_inv l.r p));
  };
  unfold core_lock_inv;
  Box.free l.r;
  drop_ (maybe _ _); //leaks p; see previous exercise on how to prevent this
}



ghost
fn share #p #q (l:lock p)
requires lock_live l #q
ensures lock_live l #(half_perm q) ** lock_live l #(half_perm q)
{
  unfold (lock_live l #q);
  GR.share l.live;
  fold (lock_live l #(half_perm q));
  fold (lock_live l #(half_perm q));
}


let sum_halves (x y:perm)
 : Lemma (ensures sum_perm (half_perm x) (half_perm y) == half_perm (sum_perm x y))
         [SMTPat (sum_perm (half_perm x) (half_perm y))]
 = let open FStar.Real in
   assert (forall (x y:FStar.Real.real). ( x /. 2.0R ) +. (y /. 2.0R) == ((x +. y) /. 2.0R))


ghost
fn gather #p #q1 #q2 (l:lock p)
requires lock_live l #q1 ** lock_live l #q2
ensures lock_live l #(sum_perm q1 q2)
{
  unfold (lock_live l #q1);
  unfold (lock_live l #q2);
  GR.gather l.live;
  fold (lock_live l #(sum_perm q1 q2));
}



fn acquire #p #q (l:lock p)
requires lock_live l #q 
ensures p ** lock_live l #q
{
    admit()
}



fn release #p #q (l:lock p)
requires p ** lock_live l #q 
ensures lock_live l #q
{
    admit()
}


