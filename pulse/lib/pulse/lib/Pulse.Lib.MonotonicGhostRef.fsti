module Pulse.Lib.MonotonicGhostRef
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.GhostPCMReference
open FStar.Preorder

let as_prop (t:Type0) = t <==> True

[@@erasable]
val mref (#t:Type0) (p:preorder t) : Type0

instance val non_informative_mref
  (t:Type u#0) (p:preorder t)
  : NonInformative.non_informative (mref p)

val pts_to (#t:Type) 
           (#p:preorder t) 
           ([@@@mkey] r:mref p)
           (#f:perm)
           (v:t)
: slprop

val pts_to_is_timeless (#t:Type) (#p:preorder t) (r:mref p) (#f:perm) (v:t)
: Lemma (timeless (pts_to r #f v))
        [SMTPat (timeless (pts_to r #f v))]

val snapshot (#t:Type)
             (#p:preorder t) 
             (r:mref p)
             (v:t)
: slprop

val snapshot_is_timeless (#t:Type) (#p:preorder t) (r:mref p) (v:t)
: Lemma (timeless (snapshot r v))
        [SMTPat (timeless (snapshot r v))]

  
ghost
fn alloc (#t:Type0) (#p:preorder t) (v:t)
  requires emp
  returns r:mref p
  ensures pts_to r #1.0R v

ghost
fn share (#t:Type0) (#p:preorder t) (r:mref p) (#v:t) (#q #f #g:perm)
  requires pts_to r #q v ** pure (q == f +. g)
  ensures pts_to r #f v ** pts_to r #g v

ghost
fn gather (#t:Type0) (#p:preorder t) (r:mref p) (#v:t) (#f #g:perm)
  requires pts_to r #f v ** pts_to r #g v
  ensures pts_to r #(f +. g) v

ghost
fn take_snapshot (#t:Type) (#p:preorder t) (r:mref p) (#f:perm) (v:t)
  requires pts_to r #f v
  ensures pts_to r #f v ** snapshot r v
 
ghost
fn recall_snapshot (#t:Type) (#p:preorder t) (r:mref p) (#f:perm) (#v #u:t)
  requires pts_to r #f v ** snapshot r u
  ensures  pts_to r #f v ** snapshot r u ** pure (as_prop (p u v))

ghost
fn dup_snapshot (#t:Type) (#p:preorder t) (r:mref p) (#u:t)
  requires snapshot r u
  ensures snapshot r u ** snapshot r u

ghost
fn update (#t:Type) (#p:preorder t) (r:mref p) (#u:t) (v:t)
  requires pts_to r #1.0R u ** pure (as_prop (p u v))
  ensures pts_to r #1.0R v
