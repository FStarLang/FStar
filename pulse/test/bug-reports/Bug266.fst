module Bug266

#lang-pulse
open Pulse

[@@expect_failure]
fn
test_intro (_:unit)
{
  intro_exists (fun () -> pure False) ();
  admit()
}

let post () = emp
assume
val my_intro (p : prop)
  : stt_ghost unit emp_inames (pure p) post

(* Should fail! Pulse is not actually applying my_intro. *)
fn
test_my_intro (_:unit)
{
  my_intro False;
  admit()
}
