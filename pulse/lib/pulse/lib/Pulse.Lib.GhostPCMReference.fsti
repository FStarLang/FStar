module Pulse.Lib.GhostPCMReference
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.PCM

let gref (#a:Type0) (p:pcm a)
: Type0
= ghost_pcm_ref #a p

val pts_to
    (#a:Type u#0)
    (#p:pcm a)
    ([@@@mkey]r:gref p)
    (v:a)
: slprop

val pts_to_is_timeless
    (#a:Type u#0)
    (#p:pcm a)
    (r:gref p)
    (v:a)
: Lemma (timeless (pts_to r v))
        [SMTPat (timeless (pts_to r v))]
        
ghost 
fn alloc
    (#a:Type u#0)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
  requires emp
  returns  r : gref pcm
  ensures  pts_to r x

ghost 
fn read
    (#a:Type)
    (#p:pcm a)
    (r:gref p)
    (x:a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
                    
  requires pts_to r x
  returns  v : (v:a{compatible p x v /\ p.refine v})
  ensures  pts_to r (f v)

ghost
fn read_simple
    (#a:Type)
    (#p:pcm a)
    (r:gref p)
    (#x:a)
  requires pts_to r x
  returns  v : (v:a{compatible p x v /\ p.refine v})
  ensures  pts_to r x

ghost
fn write
    (#a:Type)
    (#p:pcm a)
    (r:gref p)
    (x y:a)
    (f:FStar.PCM.frame_preserving_upd p x y)
  requires pts_to r x
  ensures  pts_to r y

ghost
fn share
    (#a:Type)
    (#pcm:pcm a)
    (r:gref pcm)
    (v0:a)
    (v1:a{composable pcm v0 v1})
  requires pts_to r (v0 `op pcm` v1)
  ensures  pts_to r v0 ** pts_to r v1

[@@allow_ambiguous]
ghost
fn gather
    (#a:Type)
    (#pcm:pcm a)
    (r:gref pcm)
    (v0:a)
    (v1:a)
  requires pts_to r v0 ** pts_to r v1
  returns  squash (composable pcm v0 v1)
  ensures  pts_to r (op pcm v0 v1)
