module Pulse.Lib.MonotonicGhostRef
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.GhostPCMReference
open FStar.Preorder
module GR = Pulse.Lib.GhostPCMReference
module FP = Pulse.Lib.PCM.FractionalPreorder
module PP = PulseCore.Preorder


let mref (#t:Type) (p:preorder t) = GR.gref (FP.fp_pcm p)

instance non_informative_mref t p = {
  reveal = (fun r -> Ghost.reveal r) <: NonInformative.revealer (mref p);
}

let pts_to (#t:Type) 
           (#p:preorder t) 
           (r:mref p)
           (#f:perm)
           (v:t)
= exists* h. 
    GR.pts_to r (Some f, h) **
    pure (f <=. 1.0R /\ Cons? h /\ PulseCore.Preorder.curval h == v)

let snapshot (#t:Type)
             (#p:preorder t) 
             (r:mref p)
             (v:t)
= exists* h.
    GR.pts_to r (None, h) **
    pure (Cons? h /\ PulseCore.Preorder.curval h == v)
  
let full (#t:Type) (#p:preorder t) (v:t) : FP.pcm_carrier p = 
  (Some 1.0R, [v])

ghost
fn alloc (#t:Type0) (#p:preorder t) (v:t)
requires emp
returns r:mref p
ensures pts_to r #1.0R v
{
  let r = alloc #_ #(FP.fp_pcm p) (full v);
  fold (pts_to r #1.0R v);
  r
}

ghost
fn share (#t:Type0) (#p:preorder t) (r:mref p) (#v:t) (#q #f #g:perm)
requires pts_to r #q v ** pure (q == f +. g)
ensures pts_to r #f v ** pts_to r #g v
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
requires pts_to r #f v ** pts_to r #g v
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
fn take_snapshot (#t:Type) (#p:preorder t) (r:mref p) (#f:perm) (v:t)
requires pts_to r #f v
ensures pts_to r #f v ** snapshot r v
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
requires pts_to r #f v ** snapshot r u
ensures  pts_to r #f v ** snapshot r u ** pure (as_prop (p u v))
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
fn dup_snapshot (#t:Type) (#p:preorder t) (r:mref p) (#u:t)
requires snapshot r u
ensures snapshot r u ** snapshot r u
{
  unfold snapshot;
  with h. assert (GR.pts_to r (None, h));
  GR.share r (None, h) (None, h);
  fold (snapshot r u);
  fold (snapshot r u);
}

ghost
fn update (#t:Type) (#p:preorder t) (r:mref p) (#u:t) (v:t)
requires pts_to r #1.0R u ** pure (as_prop (p u v))
ensures pts_to r #1.0R v
{
  unfold pts_to;
  with f h. assert (GR.pts_to r (f, h));
  GR.write r _ _ (FP.mk_frame_preserving_upd p h v);
  fold pts_to;
}