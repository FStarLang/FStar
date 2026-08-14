module JoinExists
#lang-pulse
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference

(* Joining the postconditions of a conditional whose branches bind existentials.
   Each of these fails outright if the join gives up and emits an opaque
   [if b then .. else ..], because nothing at all can be taken out of such a
   context -- not even a frame neither branch touched. *)

assume val f (r:R.ref int) (#v:erased int)
: stt int (R.pts_to r v) (fun x -> exists* w. R.pts_to r w ** pure (x >= 0))

assume val g (r:R.ref int) (#v:erased int)
: stt int (R.pts_to r v) (fun x -> exists* w. R.pts_to r w ** pure (x <= 0))

(* A frame neither branch mentions comes out of the conditional. *)
fn frame_survives (b:bool) (r:R.ref int) (frame:R.ref int) (#v #fv:erased int)
requires R.pts_to r v ** R.pts_to frame fv
returns x:int
ensures exists* w. R.pts_to r w ** R.pts_to frame fv
{
  let x = if b { f r } else { g r };
  x
}

(* A conjunct that differs only in the value each branch bound comes out under
   a single new binder. *)
fn bound_value_generalizes (b:bool) (r:R.ref int) (#v:erased int)
requires R.pts_to r v
returns x:int
ensures exists* w. R.pts_to r w
{
  let x = if b { f r } else { g r };
  x
}

(* Only one branch binds anything; the other leaves the reference alone. *)
fn one_sided (b:bool) (r:R.ref int) (frame:R.ref int) (#v #fv:erased int)
requires R.pts_to r v ** R.pts_to frame fv
returns x:int
ensures exists* w. R.pts_to r w ** R.pts_to frame fv
{
  let x = if b { f r } else { 0 };
  x
}

(* What each branch established as a pure fact survives, guarded by the branch
   condition. *)
fn pures_survive (b:bool) (r:R.ref int) (#v:erased int)
requires R.pts_to r v
returns x:int
ensures exists* w. R.pts_to r w ** pure (x >= 0 \/ x <= 0)
{
  let x = if b { f r } else { g r };
  x
}
