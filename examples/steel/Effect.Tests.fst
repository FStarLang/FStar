module Effect.Tests

open Steel.EffectX
open Steel.Memory

open Frame

assume val r1 : slprop
assume val r2 : slprop
assume val r3 : slprop

assume val f1 (_:unit) : SteelXT unit r1 (fun _ -> r1)
assume val f12 (_:unit) : SteelXT unit (r1 `star` r2) (fun _ -> r1 `star` r2)
assume val f123 (_:unit) : SteelXT unit ((r1 `star` r2) `star` r3) (fun _ -> (r1 `star` r2) `star` r3)

module T = FStar.Tactics

let test_frame1 (_:unit)
: SteelXT unit ((r1 `star` r2) `star` r3) (fun _ -> (r1 `star` r2) `star` r3)
= steel_frame_t f12;
  steel_frame_t f1;
  steel_frame_t f123;
  steel_frame_t f1;
  rassert ((r1 `star` r2) `star` r3)

(*
 * A crash testcase
 *)

assume
val crash_h_commute (p:slprop)
  : SteelXT unit emp (fun _ -> p)

assume
val crash_h_assert (_:unit)
  : SteelXT unit emp (fun _ -> emp)

assume val crash_get_prop : int -> slprop

[@@expect_failure]
let crash_test (_:unit)
  : SteelT unit emp (fun _ -> emp)
  = let r = 0 in
    crash_h_commute (crash_get_prop r);
    crash_h_assert ()


(**** moving the test case from Steel.ReshuffleFailure.ftst in ulib ****)

open FStar.PCM
module SB = Steel.SteelXT.Basics
module ST = Steel.Memory.Tactics

assume
val pp : int -> slprop u#1

assume
val act (a b:slprop)
  : SteelXT int (a `star` b) (fun x -> a `star` pp x)

let test (p q:slprop)
  : SteelXT int (p `star` q) (fun x -> pp x `star` q)
  = ST.reshuffle();
    let x = act q p in
    ST.reshuffle #_ #_// (pp x `star` q) //needs this annotation
  ();
    SB.return x
