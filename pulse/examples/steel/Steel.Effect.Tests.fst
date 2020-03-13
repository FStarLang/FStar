module Steel.Effect.Tests

open Steel.Effect
open Steel.Memory

assume val r1 : hprop
assume val r2 : hprop
assume val r3 : hprop

assume val f1 (_:unit) : SteelT unit r1 (fun _ -> r1)
assume val f12 (_:unit) : SteelT unit (r1 `star` r2) (fun _ -> r1 `star` r2)
assume val f123 (_:unit) : SteelT unit ((r1 `star` r2) `star` r3) (fun _ -> (r1 `star` r2) `star` r3)

module T = FStar.Tactics

let test_frame1 (_:unit)
: SteelT unit ((r1 `star` r2) `star` r3) (fun _ -> (r1 `star` r2) `star` r3)
= steel_frame_t f12;
  steel_frame_t f1;
  steel_frame_t f123;
  steel_frame_t f1;
  rassert ((r1 `star` r2) `star` r3)

(*
 * A crash testcase
 *)

assume
val crash_h_commute (p:hprop)
  : SteelT unit emp (fun _ -> p)

assume
val crash_h_assert (_:unit)
  : SteelT unit emp (fun _ -> emp)

assume val crash_get_prop : int -> hprop

[@expect_failure]
let crash_test (_:unit)
  : SteelT unit emp (fun _ -> emp)
  = let r = 0 in
    crash_h_commute (crash_get_prop r);
    crash_h_assert ()
