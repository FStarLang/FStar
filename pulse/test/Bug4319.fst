module Bug4319
open Pulse
#lang-pulse

(* https://github.com/FStarLang/FStar/issues/4319

   After an [if] whose branch writes an array cell, the inferred join left the
   array's [pts_to] under a [match] on the condition, so [live arr] could not
   be proved after it. *)

fn coin_toss () returns _: bool { true }

fn foo (arr: array bool)
  requires arr |-> 'varr
  requires pure (Seq.length 'varr == 10)
  ensures live arr
{
  if (coin_toss ()) {
    arr.(5sz) <- true;
  };
  assert live arr;
}

(* The repro from the issue, verbatim. [assert live arr] now goes through. What
   still fails is the postcondition [arr |-> 'varr], which is false when the
   branch writes the cell. *)
[@@expect_failure [19]]
fn foo_preserves (arr: array bool)
  preserves arr |-> 'varr
  requires pure (Seq.length 'varr == 10)
{
  if (coin_toss ()) {
    arr.(5sz) <- true;
  };
  assert live arr;
}

(* The array can still be written after the join. *)
fn foo_use (arr: array bool)
  requires arr |-> 'varr
  requires pure (Seq.length 'varr == 10)
  ensures exists* v. (arr |-> v) ** pure (Seq.length v == 10 /\ Seq.index v 5 == false)
{
  pts_to_len arr;
  if (coin_toss ()) {
    arr.(5sz) <- true;
  };
  pts_to_len arr;
  arr.(5sz) <- false;
}
