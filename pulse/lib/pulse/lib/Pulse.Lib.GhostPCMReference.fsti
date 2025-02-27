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
        
val alloc
    (#a:Type u#0)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: stt_ghost (gref pcm)
    emp_inames
    emp
    (fun r -> pts_to r x)

val read
    (#a:Type)
    (#p:pcm a)
    (r:gref p)
    (x:a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: stt_ghost (v:a{compatible p x v /\ p.refine v})
    emp_inames
    (pts_to r x)
    (fun v -> pts_to r (f v))

val read_simple
    (#a:Type)
    (#p:pcm a)
    (r:gref p)
    (#x:a)
: stt_ghost (v:a{compatible p x v /\ p.refine v})
    emp_inames
    (pts_to r x)
    (fun v -> pts_to r x)

val write
    (#a:Type)
    (#p:pcm a)
    (r:gref p)
    (x y:a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt_ghost unit
    emp_inames
    (pts_to r x)
    (fun _ -> pts_to r y)

val share
    (#a:Type)
    (#pcm:pcm a)
    (r:gref pcm)
    (v0:a)
    (v1:a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames
    (pts_to r (v0 `op pcm` v1))
    (fun _ -> pts_to r v0 ** pts_to r v1)

[@@allow_ambiguous]
val gather
    (#a:Type)
    (#pcm:pcm a)
    (r:gref pcm)
    (v0:a)
    (v1:a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (pts_to r v0 ** pts_to r v1)
    (fun _ -> pts_to r (op pcm v0 v1))
