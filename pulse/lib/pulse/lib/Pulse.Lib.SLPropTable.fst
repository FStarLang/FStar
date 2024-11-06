module Pulse.Lib.SLPropTable
#lang-pulse
open Pulse.Lib.Pervasives
module GT = Pulse.Lib.GhostFractionalTable
let table = GT.table slprop_ref

instance non_informative_table
: NonInformative.non_informative table
= _ by (FStar.Tactics.Typeclasses.tcresolve())

[@@pulse_unfold]
let is_table (t:table) (max:nat)
: slprop
= GT.is_table t max

let pts_to (t:table) (i:nat) (#f:perm) (p:slprop)
: slprop
= exists* r.
    slprop_ref_pts_to r p **
    GT.pts_to t i #f r

ghost
fn create ()
requires emp
returns t:table
ensures is_table t 0
{
  let t = GT.create #slprop_ref;
  t
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
  drop_ (slprop_ref_pts_to _ _);
  let r' = slprop_ref_alloc p;
  GT.update t r';
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
  let r = slprop_ref_alloc p;
  GT.alloc t r;
  fold pts_to;
}


ghost
fn in_bounds (t:table) (#i:nat) (#f:perm) (#p:slprop) (#n:nat)
requires
  is_table t n ** pts_to t i #f p
ensures
  is_table t n ** pts_to t i #f p ** pure (i < n)
{
  unfold pts_to;
  GT.in_bounds t;
  fold pts_to;
}

ghost
fn share (t:table) i (f0 f1:perm) (#f:perm) (#p:slprop)
requires 
  pts_to t i #f p ** pure (f == f0 +. f1)
ensures
  pts_to t i #f0 p ** pts_to t i #f1 p
{
  unfold pts_to;
  GT.share t i f0 f1;
  slprop_ref_share _;
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
  with r0. assert (GT.pts_to t i #f0 r0);
  unfold pts_to;
  with r1. assert (GT.pts_to t i #f1 r1);
  GT.gather t i #f0 #f1 #r0 #r1;
  slprop_ref_gather r0 #p #q;
  fold (pts_to t i #(f0 +. f1) p);
}