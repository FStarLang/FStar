module Bug4890
#lang-pulse
open Pulse
module R = Pulse.Lib.Reference
module Seq = FStar.Seq
module U8 = FStar.UInt8

(* Relating [cell r s] to [cell r (Seq.create 1 0uy)] needs [s == Seq.create
   1 0uy] for both conjuncts of the [pure]. Core's guard cache used to claim
   it had been emitted for the first conjunct, where it was only one side of
   a disjunction, so the second conjunct's identical obligation was dropped,
   and the false equation proven. *)
let cell ([@@@mkey] r: R.ref U8.t) (xs: Seq.seq U8.t) : slprop =
  exists* v. R.pts_to r v ** pure (Seq.length xs == 1 /\ Seq.index xs 0 == v)

[@@expect_failure [19]]
fn becomes_zero (r: R.ref U8.t) (#s: erased (x: Seq.seq U8.t { Seq.length x == 1 }))
  requires cell r s
  ensures cell r (Seq.create 1 0uy)
{ () }

fn stays (r: R.ref U8.t) (#s: erased (x: Seq.seq U8.t { Seq.length x == 1 }))
  requires cell r s ** pure (Seq.index s 0 == 0uy)
  ensures cell r (Seq.create 1 0uy)
{
  assert pure (Seq.equal s (Seq.create 1 0uy));
}
