module Pulse.Lib.GhostFractionalTable
#lang-pulse
open Pulse.Lib.Pervasives
module PM = Pulse.Lib.PCM.Map
module PF = Pulse.Lib.PCM.Fraction
module GPR = Pulse.Lib.GhostPCMReference
let a_map (a:Type) = PM.pointwise nat (PF.pcm_frac #(option a))
let carrier a = PM.map nat (PF.fractional (option a))
let tab a = GPR.gref (a_map a)
[@@erasable]
let table a = erased (tab a)

instance non_informative_table a : NonInformative.non_informative (table a) = {
  reveal = (fun (x:erased (table a)) -> FStar.Ghost.reveal x)
}

let full_perm : perm = 1.0R
let full_table_above #a (n:nat)
: carrier a
= Map.map_literal 
  (fun (k:nat) -> 
    if k < n
    then None
    else Some (None, full_perm))

let singleton #a (i:nat) (f:perm) (r:option a)
: carrier a
= Map.map_literal
  (fun (k:nat) -> 
    if k = i
    then Some (r, f)
    else None)

let is_table #a ([@@@mkey]t:table a) (max:nat)
: slprop
= GPR.pts_to t (full_table_above max)

let placeless_is_table #a t max = Tactics.Typeclasses.solve

let pts_to #a (t:table a) (i:nat) (#f:perm) (p:a)
: slprop
= GPR.pts_to t (singleton i f (Some p)) **
  pure (PF.perm_ok f)

let placeless_pts_to #a t i #f p = Tactics.Typeclasses.solve

ghost
fn create (#a:Type)
  returns t:table a
  ensures is_table t 0
{
  let gref = GPR.alloc #_ #(a_map a) (full_table_above 0);
  fold (is_table gref 0);
  gref
}

let fp_upd_singleton (#a:Type) (i:nat) (r0 r1:option a)
: FStar.PCM.frame_preserving_upd
    (a_map a)
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
fn update #a (t:table a) (#i:nat) (#old:a) (p: a)
requires 
  pts_to t i #full_perm old
ensures
  pts_to t i #full_perm p
{
  unfold pts_to;
  GPR.write t _ _ (fp_upd_singleton i (Some old) (Some p));
  fold pts_to;
}

ghost
fn take_i (#a:Type0) (r:GPR.gref (a_map a)) (n:nat)
requires 
  GPR.pts_to r (full_table_above n)
ensures
  GPR.pts_to r (full_table_above (n + 1)) **
  GPR.pts_to r (singleton n full_perm None)
{
  assert pure (
    Map.equal 
      (full_table_above n)
      (full_table_above (n + 1) `FStar.PCM.op (a_map a)` singleton n full_perm None)
  );
  GPR.share r (full_table_above (n + 1)) (singleton n full_perm None)
}


ghost
fn alloc #a (t:table a) (p:a) (#i:nat)
requires
  is_table t i
ensures
  is_table t (i + 1) **
  pts_to t i #1.0R p
{
  unfold is_table;
  take_i t i;
  GPR.write t _ _ (fp_upd_singleton i None (Some p));
  fold pts_to;
  fold is_table;
}

ghost
fn in_bounds #a (t:table a) (#i:nat) (#f:perm) (#p:a) (#n:nat)
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
fn share #a (t:table a) i (f0 f1:perm) (#f:perm) (#p:a)
requires 
  pts_to t i #f p ** pure (f == f0 +. f1)
ensures
  pts_to t i #f0 p ** pts_to t i #f1 p
{
  unfold pts_to;
  assert pure (
    Map.equal 
      (singleton i (f0 +. f1) (Some p))
      (singleton i f0 (Some p) `FStar.PCM.op (a_map a)` singleton i f1 (Some p))
  );
  GPR.share t (singleton i f0 (Some p)) (singleton i f1 (Some p));
  fold (pts_to t i #f0 p);
  fold (pts_to t i #f1 p)
}

ghost
fn gather #a (t:table a) (i:nat) (#f0 #f1:perm ) (#p #q:a)
requires 
   pts_to t i #f0 p ** pts_to t i #f1 q
ensures
   pts_to t i #(f0 +. f1) p ** pure (p == q)
{
  unfold (pts_to t i #f0 p);
  unfold pts_to;
  GPR.gather t (singleton i f0 (Some p)) (singleton i f1 (Some q));
  assert pure (
    Map.equal 
      (singleton i (f0 +. f1) (Some p))
      (singleton i f0 (Some p) `FStar.PCM.op (a_map a)` singleton i f1 (Some q))
  );
  fold (pts_to t i #(f0 +. f1) p);
}
