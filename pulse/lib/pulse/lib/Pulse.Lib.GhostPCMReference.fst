module Pulse.Lib.GhostPCMReference
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.PCM
module PR = Pulse.Lib.PCM.Raise
module U = FStar.Universe

let pts_to
    (#a:Type u#0)
    (#p:pcm a)
    (r:gref p)
    (v:a)
: slprop
= ghost_pcm_pts_to #_ #(PR.raise p) r (U.raise_val v)

let pts_to_is_timeless #a #p r v = ()

let alloc #a #p x = ghost_alloc #_ #(PR.raise p) (U.raise_val x)
  

ghost
fn read
    (#a:Type u#0)
    (#p:pcm a)
    (r:gref p)
    (x:a)
    (f: (v:a{FStar.PCM.compatible #a p (reveal x) v}
          -> GTot (y:a{compatible p y v /\
                        FStar.PCM.frame_compatible p x v y})))
requires pts_to r x
returns v:(v:a { compatible p x v /\ p.refine v })
ensures pts_to r (f v) 
{
  unfold pts_to;
  rewrite ghost_pcm_pts_to #_ #(PR.raise p) r (U.raise_val u#0 u#1 x)
      as ghost_pcm_pts_to #_ #(PR.raise p) r (reveal (hide (U.raise_val x)));
  let v = ghost_read #_ #(PR.raise u#0 u#1 p) r (U.raise_val x) (PR.raise_refine u#0 u#1 p x f);
  let v = U.downgrade_val (Ghost.reveal v);
  with _v. 
   rewrite ghost_pcm_pts_to #(U.raise_t u#0 u#1 a) #(PR.raise p) r _v
        as ghost_pcm_pts_to #_ #(PR.raise p) r (U.raise_val u#0 u#1 (f v));
  fold (pts_to r (f v));
  v
}


let identity_frame_compatible
      #a (p:FStar.PCM.pcm a)
      (x:a)
      (v:a{FStar.PCM.compatible p x v})
: y:a { FStar.PCM.compatible p y v /\ FStar.PCM.frame_compatible p x v y }
= x

let read_simple
    (#a:Type)
    (#p:pcm a)
    (r:gref p)
    (#x:a)
= read #a #p r x (identity_frame_compatible p x)

let write
    (#a:Type)
    (#p:pcm a)
    (r:gref p)
    (x y:a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt_ghost unit
    emp_inames
    (pts_to r x)
    (fun _ -> pts_to r y)
= ghost_write #_ #(PR.raise p) r (U.raise_val x) (U.raise_val y)
                 (PR.raise_upd f)

let share
    (#a:Type)
    (#pcm:pcm a)
    (r:gref pcm)
    (v0:a)
    (v1:a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames
    (pts_to r (v0 `op pcm` v1))
    (fun _ -> pts_to r v0 ** pts_to r v1)
= ghost_share #_ #(PR.raise pcm) r (U.raise_val v0) (U.raise_val v1)

let gather
    (#a:Type)
    (#pcm:pcm a)
    (r:gref pcm)
    (v0 v1:a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (pts_to r v0 ** pts_to r v1)
    (fun _ -> pts_to r (op pcm v0 v1))
= ghost_gather #_ #(PR.raise pcm) r (U.raise_val v0) (U.raise_val v1)
