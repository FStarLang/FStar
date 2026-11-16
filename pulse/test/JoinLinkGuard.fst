module JoinLinkGuard
#lang-pulse
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference

(* The "then" branch moves the cell to a fresh value [y], known through a
   pure fact, and trades [q] for [p]. The cell is joined with the "else"
   branch's and the link states the fact; [p] and [q] stay under the
   condition. The fact must not stay there too: [y] is not mentioned by [p],
   so nothing would determine a witness for it. *)

assume val ok : int -> prop
assume val p : slprop
assume val q : slprop

assume val step (r:R.ref int) (#v:erased int)
: stt unit (R.pts_to r v ** q) (fun _ -> exists* y. R.pts_to r y ** p ** pure (ok y))

fn step_if (b:bool) (r:R.ref int) (#v:erased int)
requires R.pts_to r v ** q ** pure (ok v)
ensures exists* w. R.pts_to r w ** pure (ok w) ** (match b with | true -> p | false -> q)
{
  if b { step r } else { () };
  ()
}

fn step_unless (b:bool) (r:R.ref int) (#v:erased int)
requires R.pts_to r v ** q ** pure (ok v)
ensures exists* w. R.pts_to r w ** pure (ok w) ** (match b with | true -> q | false -> p)
{
  if b { () } else { step r };
  ()
}
