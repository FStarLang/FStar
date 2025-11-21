module Pulse.Lib.GhostFractionalTable
#lang-pulse
open Pulse.Lib.Pervasives

[@@erasable]
val table (a:Type0) : Type0

instance val non_informative_table (a:Type): NonInformative.non_informative (table a)
val is_table #a ([@@@mkey] t:table a) (max:nat) : slprop

instance val placeless_is_table #a t max : placeless (is_table #a t max)

val pts_to #a ([@@@mkey] t:table a) (i:nat) (#f:perm) (p:a) : slprop

instance val placeless_pts_to #a t i #f p : placeless (pts_to #a t i #f p)

ghost
fn create (#a:Type)
  requires emp
  returns t:table a
  ensures is_table t 0

ghost
fn update #a (t:table a) (#i:nat) (#old:a) (p: a)
  requires 
    pts_to t i #1.0R old
  ensures
    pts_to t i #1.0R p

ghost
fn alloc #a (t:table a) (p:a) (#i:nat)
  requires
    is_table t i
  ensures
    is_table t (i + 1) **
    pts_to t i #1.0R p

ghost
fn in_bounds #a (t:table a) (#i:nat) (#f:perm) (#p:a) (#n:nat)
  requires
    is_table t n ** pts_to t i #f p
  ensures
    is_table t n ** pts_to t i #f p ** pure (i < n)

ghost
fn share #a (t:table a) i (f0 f1:perm) (#f:perm) (#p:a)
  requires 
    pts_to t i #f p ** pure (f == f0 +. f1)
  ensures
    pts_to t i #f0 p ** pts_to t i #f1 p

ghost
fn gather #a (t:table a) (i:nat) (#f0 #f1:perm ) (#p #q:a)
  requires 
    pts_to t i #f0 p ** pts_to t i #f1 q
  ensures
    pts_to t i #(f0 +. f1) p ** pure (p == q)
