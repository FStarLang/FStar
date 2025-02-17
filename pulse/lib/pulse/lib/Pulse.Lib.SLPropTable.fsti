module Pulse.Lib.SLPropTable
#lang-pulse
open Pulse.Lib.Pervasives

[@@erasable]
val table : Type0

instance val non_informative_table: NonInformative.non_informative table

val is_table ([@@@mkey]t:table) (max:nat) : slprop

val pts_to ([@@@mkey]t:table) ([@@@mkey]i:nat) (#f:perm) (p:slprop) : slprop

ghost
fn create ()
requires emp
returns t:table
ensures is_table t 0

ghost
fn update (t:table) 
          (i:nat)
          (p:slprop)
requires 
  pts_to t i #1.0R 'old
ensures
  pts_to t i #1.0R p

ghost
fn alloc (t:table) (p:slprop) (#i:nat)
requires
  is_table t i
ensures
  is_table t (i + 1) **
  pts_to t i #1.0R p

ghost
fn in_bounds (t:table) (#i:nat) (#f:perm) (#p:slprop) (#n:nat)
requires
  is_table t n ** pts_to t i #f p
ensures
  is_table t n ** pts_to t i #f p ** pure (i < n)

ghost
fn share (t:table) i (f0 f1:perm) (#f:perm) (#p:slprop)
requires 
  pts_to t i #f p ** pure (f == f0 +. f1)
ensures
  pts_to t i #f0 p ** pts_to t i #f1 p

ghost
fn gather (t:table) (i:nat) (#f0 #f1:perm ) (#p #q:slprop)
requires 
   pts_to t i #f0 p ** pts_to t i #f1 q
ensures
   pts_to t i #(f0 +. f1) p ** later (equiv p q)
