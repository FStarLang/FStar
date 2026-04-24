module Pulse.Lib.MonotonicGhostRef
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.GhostPCMReference
open FStar.Preorder
module GR = Pulse.Lib.GhostPCMReference
module FP = Pulse.Lib.PCM.FractionalPreorder


let mref (#t:Type) (p:preorder t) = GR.gref (FP.fp_pcm p)

instance non_informative_mref t p = {
  reveal = (fun r -> Ghost.reveal r) <: NonInformative.revealer (mref p);
}

let pts_to_pred (#t:Type)
           (#p:preorder t) 
           (f:perm)
           (v:t)
           (h:PulseCore.Preorder.vhist p)
: prop =
    (f <=. 1.0R /\ Cons? h /\ PulseCore.Preorder.curval h == v)

[@@pulse_unfold]
let pts_to' (#t:Type)
           (#p:preorder t) 
           (r:mref p)
           (#f:perm)
           (v:t)
: timeless_slprop =
  exists* h.
    GR.pts_to r (Some f, h) **
    pure (pts_to_pred f v h)

let pts_to = pts_to'
let placeless_pts_to r v = Tactics.Typeclasses.solve
let pts_to_is_timeless (#t:Type) (#p:preorder t) (r:mref p) #f (v:t) = ()

[@@pulse_unfold]
let snapshot' (#t:Type)
              (#p:preorder t) 
              (r:mref p)
              (v:t)
: timeless_slprop =
  exists* h.
    GR.pts_to r (None, h) **
    pure (Cons? h /\ PulseCore.Preorder.curval h == v)
let snapshot #t #p r v = snapshot' #t #p r v
let placeless_snapshot r v = Tactics.Typeclasses.solve
let snapshot_is_timeless (#t:Type) (#p:preorder t) (r:mref p) (v:t) = ()
let full (#t:Type) (#p:preorder t) (v:t) : FP.pcm_carrier p = 
  (Some 1.0R, [v])

ghost
fn alloc (#t:Type0) (#p:preorder t) (v:t)
  returns r:mref p
  ensures pts_to r #1.0R v
{
  let r = alloc #_ #(FP.fp_pcm p) (full v);
  fold (pts_to r #1.0R v);
  r
}

ghost
fn share (#t:Type0) (#p:preorder t) (r:mref p) (#v:t) (#q #f #g:perm)
  requires pts_to r #q v
  requires pure (q == f +. g)
  ensures pts_to r #f v
  ensures pts_to r #g v
{
  unfold pts_to;
  with h. assert (GR.pts_to r (Some q, h));
  rewrite (GR.pts_to r (Some q, h)) as 
          (GR.pts_to r ((Some f, h) `(FP.fp_pcm p).p.op` (Some g, h)));
  GR.share r (Some f, h) (Some g, h);
  fold (pts_to r #f v);
  fold (pts_to r #g v);
}


ghost
fn gather (#t:Type0) (#p:preorder t) (r:mref p) (#v:t) (#f #g:perm)
  requires pts_to r #f v
  requires pts_to r #g v
  ensures pts_to r #(f +. g) v
{ 
  unfold (pts_to r #f v);
  with hf. assert (GR.pts_to r (Some f, hf));
  unfold pts_to;
  with hg. assert (GR.pts_to r (Some g, hg));
  GR.gather r (Some f, hf) (Some g, hg);
  rewrite (GR.pts_to r ((Some f, hf) `(FP.fp_pcm p).p.op` (Some g, hf)))
       as (GR.pts_to r (Some #perm (f +. g), hf));
  fold (pts_to r #(f +. g) v);
}

ghost
fn dup_snapshot (#t:Type) (#p:preorder t) (r:mref p) (#u:t)
  preserves snapshot r u
  ensures snapshot r u
{
  unfold snapshot;
  with h. assert (GR.pts_to r (None, h));
  GR.share r (None, h) (None, h);
  fold (snapshot r u);
  fold (snapshot r u);
}

instance duplicable_snapshot #t #p r u : duplicable (snapshot #t #p r u) =
  { dup_f = fun _ -> dup_snapshot r #u }

ghost
fn take_snapshot (#t:Type) (#p:preorder t) (r:mref p) (#f:perm) (v:t)
  preserves pts_to r #f v
  ensures snapshot r v
{
  unfold pts_to;
  with h. assert (GR.pts_to r (Some f, h));
  rewrite (GR.pts_to r (Some f, h)) as 
          (GR.pts_to r ((Some f, h) `(FP.fp_pcm p).p.op` (None, h)));
  GR.share r (Some f, h) (None, h);
  fold (pts_to r #f v);
  fold (snapshot r v);
}

ghost
fn recall_snapshot (#t:Type) (#p:preorder t) (r:mref p) (#f:perm) (#v #u:t)
  preserves pts_to r #f v
  requires snapshot r u
  ensures pure (p u v)
{
  unfold pts_to;
  with h. assert (GR.pts_to r (Some f, h));
  unfold snapshot;
  with h'. assert (GR.pts_to r (None, h'));
  GR.gather r (Some f, h) (None, h');
  GR.share r (Some f, h) (None, h');
  fold (snapshot r u);
  fold (pts_to r #f v);
}

ghost
fn snapshots_related_alt (#t:Type0) (#p:preorder t) (r s:mref p) (#h0 #h1: erased (PulseCore.Preorder.hist #t p))
  requires with_pure (Cons? h0 /\ Cons? h1)
  requires pure (r == s)
  preserves GR.pts_to r (None, reveal h0)
  preserves GR.pts_to s (None, reveal h1)
  ensures pure (
    p (PulseCore.Preorder.curval h0) (PulseCore.Preorder.curval h1) \/
    p (PulseCore.Preorder.curval h1) (PulseCore.Preorder.curval h0)
  )
{ 
  rewrite each s as r;
  GR.gather r _ _;
  GR.share r _ _;
  rewrite (GR.pts_to r (None, reveal h1)) as (GR.pts_to s (None, reveal h1));
}

ghost
fn snapshots_related (#t:Type0) (#p:preorder t) (r:mref p) (#u #v:t)
  preserves snapshot r u
  preserves snapshot r v
  ensures pure (
    p u v \/ p v u
  )
{
  let s = r;
  rewrite (snapshot r v) as (snapshot s v);
  unfold snapshot s v;
  unfold snapshot r u;
  with h0. assert (GR.pts_to r (None, reveal h0));
  with h1. assert (GR.pts_to s (None, reveal h1));
  snapshots_related_alt r s #h0 #h1;
  fold snapshot r u;
  fold snapshot s v;
}

ghost
fn update (#t:Type) (#p:preorder t) (r:mref p) (#u:t) (v:t)
  requires pts_to r #1.0R u
  requires pure (p u v)
  ensures pts_to r #1.0R v
{
  unfold pts_to;
  with f h. assert (GR.pts_to r (f, h));
  GR.write r _ _ (FP.mk_frame_preserving_upd p h v);
  fold pts_to r #1.0R v;
}
