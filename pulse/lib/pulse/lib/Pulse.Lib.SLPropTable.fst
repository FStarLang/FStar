module Pulse.Lib.SLPropTable
#lang-pulse
open Pulse.Lib.Pervasives
module PM = Pulse.Lib.PCMMap
module PF = Pulse.Lib.PCM.Fraction
module GR = Pulse.Lib.GhostReference
module GPR = Pulse.Lib.GhostPCMReference
let slprop_map = PM.pointwise nat (PF.pcm_frac #really_big_ref)
let carrier = PM.map nat (PF.fractional really_big_ref)
let tab = GPR.gref slprop_map

[@@erasable]
let table = erased tab

instance non_informative_table: NonInformative.non_informative table = {
  reveal = (fun (x:erased table) -> FStar.Ghost.reveal x)
}

let full_perm : perm = 1.0R
let full_table_above (n:nat) (r:really_big_ref)
: carrier
= Map.map_literal 
  (fun (k:nat) -> 
    if k < n
    then None
    else Some (r, full_perm))

let singleton (i:nat) (f:perm) (r:really_big_ref) 
: carrier
= Map.map_literal
  (fun (k:nat) -> 
    if k = i
    then Some (r, f)
    else None)

let is_table (t:table) (max:nat)
: slprop
= exists* default_r.
    GPR.pts_to t (full_table_above max default_r)

let pts_to (t:table) (i:nat) (#f:perm) (p:slprop)
: slprop
= exists* r.
    really_big_pts_to r p **
    GPR.pts_to t (singleton i f r) **
    pure (PF.perm_ok f)

ghost
fn create ()
requires emp
returns t:table
ensures is_table t 0
{
  // let max : GR.ref nat = GR.alloc #nat 0;
  let default_r = really_big_alloc emp;
  drop_ (really_big_pts_to _ _);
  let gref = GPR.alloc #_ #slprop_map (full_table_above 0 default_r);
  fold (is_table gref 0);
  gref
}

let fp_upd_singleton (i:nat) (r0 r1:really_big_ref)
: FStar.PCM.frame_preserving_upd
    slprop_map
    (singleton i full_perm r0)
    (singleton i full_perm r1)
= let fp = PF.mk_frame_preserving_upd r0 r1 in
  let fp = PM.lift_frame_preserving_upd _ _ fp (singleton i full_perm r0) i in
  assert (
    Map.equal (singleton i full_perm r1)
              (Map.upd (singleton i full_perm r0) i (Some (r1, full_perm)))
  );
  fp

ghost
fn update_i (r:GPR.gref slprop_map) (i:nat) (f:perm) (r0 r1: really_big_ref)
requires 
  GPR.pts_to r (singleton i full_perm r0)
ensures
  GPR.pts_to r (singleton i full_perm r1)
{
  GPR.write r _ _ (fp_upd_singleton i r0 r1);
}

ghost
fn share_i (r:GPR.gref slprop_map) (i:nat) (f0 f1:perm) (v: really_big_ref)
requires 
  GPR.pts_to r (singleton i (f0 +. f1) v) ** pure (PF.perm_ok (f0 +. f1))
ensures
  GPR.pts_to r (singleton i f0 v) **
  GPR.pts_to r (singleton i f1 v)
{
  assert pure (
    Map.equal 
      (singleton i (f0 +. f1) v)
      (singleton i f0 v `FStar.PCM.op slprop_map` singleton i f1 v)
  );
  GPR.share r (singleton i f0 v) (singleton i f1 v)
}

ghost
fn gather_i (r:GPR.gref slprop_map) (i:nat) (f0 f1:perm) (v0 v1: really_big_ref)
requires 
  GPR.pts_to r (singleton i f0 v0) **
  GPR.pts_to r (singleton i f1 v1)
ensures
  GPR.pts_to r (singleton i (f0 +. f1) v0) **
  pure (v0 == v1 /\ PF.perm_ok (f0 +. f1))
{
  GPR.gather r (singleton i f0 v0) (singleton i f1 v1);
  assert pure (
    Map.equal 
      (singleton i (f0 +. f1) v0)
      (singleton i f0 v0 `FStar.PCM.op slprop_map` singleton i f1 v1)
  )
}

ghost
fn take_i (r:GPR.gref slprop_map) (n:nat) (#dr:_)
requires 
  GPR.pts_to r (full_table_above n dr)
ensures
  GPR.pts_to r (full_table_above (n + 1) dr) **
  GPR.pts_to r (singleton n full_perm dr)
{
  assert pure (
    Map.equal 
      (full_table_above n dr)
      (full_table_above (n + 1) dr `FStar.PCM.op slprop_map` singleton n full_perm dr)
  );
  GPR.share r (full_table_above (n + 1) dr) (singleton n full_perm dr)
}

ghost
fn update
          (t:table) 
          (i:nat)
          (p:slprop)
requires 
  pts_to t i #1.0R 'old
ensures
  pts_to t i #1.0R p
{
  unfold pts_to;
  drop_ (really_big_pts_to _ _);
  let r' = really_big_alloc p;
  update_i t i full_perm _ r';
  fold pts_to
}

ghost
fn alloc (t:table) (p:slprop) (#i:nat)
requires
  is_table t i
ensures
  is_table t (i + 1) **
  pts_to t i #1.0R p
{
  unfold is_table;
  take_i t i;
  let r = really_big_alloc p;
  update_i t i full_perm _ r;
  fold pts_to;
  fold is_table;
}


ghost
fn in_bounds (t:table) (#i:nat) (#f:perm) (#p:slprop) (#n:nat)
requires
  is_table t n ** pts_to t i #f p
ensures
  is_table t n ** pts_to t i #f p ** pure (i < n)
{
  if (i >= n) 
  {
    unfold is_table;
    unfold pts_to;
    GPR.gather t _ _;
    unreachable()
  }
}

ghost
fn share (t:table) i (f0 f1:perm) (#f:perm) (#p:slprop)
requires 
  pts_to t i #f p ** pure (f == f0 +. f1)
ensures
  pts_to t i #f0 p ** pts_to t i #f1 p
{
  unfold pts_to;
  with r. assert (GPR.pts_to t (singleton i f r));
  share_i t i f0 f1 r;
  really_big_share _;
  fold (pts_to t i #f0 p);
  fold pts_to;
}

ghost
fn gather (t:table) (i:nat) (#f0 #f1:perm ) (#p #q:slprop)
requires 
   pts_to t i #f0 p ** pts_to t i #f1 q
ensures
   pts_to t i #(f0 +. f1) p ** later (equiv p q)
{
  unfold (pts_to t i #f0 p);
  with r0. assert (GPR.pts_to t (singleton i f0 r0));
  unfold pts_to;
  with r1. assert (GPR.pts_to t (singleton i f1 r1));
  gather_i t i f0 f1 r0 r1;
  really_big_gather r0 #p #q;
  fold (pts_to t i #(f0 +. f1) p);
}