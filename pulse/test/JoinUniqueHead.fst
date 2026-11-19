module JoinUniqueHead
#lang-pulse
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference

(* [own] is keyed on the value it describes, so two applications of it with
   different values are never matched by key. A branch that moves the cell to
   a fresh value [y], holding [own y], joined with one that holds [own v],
   still describes the same resource: each is the only [own] on its side.
   They must be paired, and since the cell's value and [own]'s argument are
   the same pair of terms in both branches, generalized by a single binder.
   The branches also differ in [p] and [q], so that neither branch's
   version of what is left unmatched holds of the other. *)

assume val own0 : int -> slprop
let own ([@@@mkey] x:int) : slprop = own0 x
assume val p : slprop
assume val q : slprop

assume val step (r:R.ref int) (#v:erased int)
: stt unit (R.pts_to r v ** own v ** q) (fun _ -> exists* y. R.pts_to r y ** own y ** p)

fn step_if (b:bool) (r:R.ref int) (#v:erased int)
requires R.pts_to r v ** own v ** q
ensures exists* w. R.pts_to r w ** own w ** (match b with | true -> p | false -> q)
{
  if b { step r } else { () };
  ()
}

fn step_unless (b:bool) (r:R.ref int) (#v:erased int)
requires R.pts_to r v ** own v ** q
ensures exists* w. R.pts_to r w ** own w ** (match b with | true -> q | false -> p)
{
  if b { () } else { step r };
  ()
}
