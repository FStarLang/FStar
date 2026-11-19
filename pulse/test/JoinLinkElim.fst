module JoinLinkElim
#lang-pulse
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference

(* A branch that moves several cells to fresh values, known only through pure
   facts, joined with a branch that leaves them alone. Each generalized value
   [w] stands for a hoisted variable [y] of the branch, or for [reveal y] with
   [y] erased. The link recording this must substitute [w] for [y] rather
   than quantify over [y] with an equation per cell: the SMT solver does not
   eliminate such equations on erased types by itself, and with this many
   cells the link is no longer proved. *)

assume val ok : int -> prop

assume val bump (r:R.ref int) (#v:erased int)
: stt unit (R.pts_to r v ** pure (ok v))
           (fun _ -> exists* (y:erased int). R.pts_to r (reveal y) ** pure (ok y /\ reveal y =!= reveal v))

assume val bump_plain (r:R.ref int) (#v:erased int)
: stt unit (R.pts_to r v ** pure (ok v))
           (fun _ -> exists* (y:int). R.pts_to r y ** pure (ok y /\ y =!= reveal v))

fn bump_all (b:bool) (r0 r1 r2 r3 r4 r5 r6 r7:R.ref int) (#v0 #v1 #v2 #v3 #v4 #v5 #v6 #v7:erased int)
requires R.pts_to r0 v0 **
         R.pts_to r1 v1 **
         R.pts_to r2 v2 **
         R.pts_to r3 v3 **
         R.pts_to r4 v4 **
         R.pts_to r5 v5 **
         R.pts_to r6 v6 **
         R.pts_to r7 v7 **
         pure (ok v0 /\ ok v1 /\ ok v2 /\ ok v3 /\ ok v4 /\ ok v5 /\ ok v6 /\ ok v7)
ensures exists* w0 w1 w2 w3 w4 w5 w6 w7.
         R.pts_to r0 w0 **
         R.pts_to r1 w1 **
         R.pts_to r2 w2 **
         R.pts_to r3 w3 **
         R.pts_to r4 w4 **
         R.pts_to r5 w5 **
         R.pts_to r6 w6 **
         R.pts_to r7 w7 **
         pure (ok w0 /\ ok w1 /\ ok w2 /\ ok w3 /\ ok w4 /\ ok w5 /\ ok w6 /\ ok w7)
{
  if b { bump r0; bump_plain r1; bump r2; bump_plain r3; bump r4; bump_plain r5; bump r6; bump_plain r7 } else { () };
  ()
}

fn bump_all_else (b:bool) (r0 r1 r2 r3 r4 r5 r6 r7:R.ref int) (#v0 #v1 #v2 #v3 #v4 #v5 #v6 #v7:erased int)
requires R.pts_to r0 v0 **
         R.pts_to r1 v1 **
         R.pts_to r2 v2 **
         R.pts_to r3 v3 **
         R.pts_to r4 v4 **
         R.pts_to r5 v5 **
         R.pts_to r6 v6 **
         R.pts_to r7 v7 **
         pure (ok v0 /\ ok v1 /\ ok v2 /\ ok v3 /\ ok v4 /\ ok v5 /\ ok v6 /\ ok v7)
ensures exists* w0 w1 w2 w3 w4 w5 w6 w7.
         R.pts_to r0 w0 **
         R.pts_to r1 w1 **
         R.pts_to r2 w2 **
         R.pts_to r3 w3 **
         R.pts_to r4 w4 **
         R.pts_to r5 w5 **
         R.pts_to r6 w6 **
         R.pts_to r7 w7 **
         pure (ok w0 /\ ok w1 /\ ok w2 /\ ok w3 /\ ok w4 /\ ok w5 /\ ok w6 /\ ok w7)
{
  if b { () } else { bump r0; bump_plain r1; bump r2; bump_plain r3; bump r4; bump_plain r5; bump r6; bump_plain r7 };
  ()
}
