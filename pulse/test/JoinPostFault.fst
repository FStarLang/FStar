module JoinPostFault
#lang-pulse
open Pulse
open Pulse.Lib.Reference

(* The postcondition of an `if` that is not the last statement is inferred by
   Pulse.JoinComp, which is untrusted: Pulse.Checker.If uses a candidate only
   after checking it is a well-typed slprop outside the conditional, and
   proving it of both branches.

   `--ext pulse:join_fault=<mode>` makes the inference return a wrong
   candidate (see Pulse.JoinComp.join_post_candidate). Each test below is
   accepted without the fault, and must be rejected, or accepted only when the
   wrong candidate happens to hold, with it. *)

fn writes_differ (b:bool) (r:ref int)
  requires r |-> 0
  ensures exists* v. r |-> v
{
  if (b) { r := 1; } else { r := 2; };
  ()
}

fn reads_after (b:bool) (r:ref int) (s:ref int)
  requires r |-> 0 ** s |-> 3
  ensures exists* v. r |-> v ** s |-> 3
{
  if (b) { r := 1; } else { () };
  let x = !s;
  assert (pure (x == 3));
  ()
}

(* `pure False` holds in neither branch. *)
#push-options "--ext pulse:join_fault=false"
[@@expect_failure [19]]
fn writes_differ_false (b:bool) (r:ref int)
  requires r |-> 0
  ensures exists* v. r |-> v
{
  if (b) { r := 1; } else { r := 2; };
  ()
}

[@@expect_failure [19]]
fn reads_after_false (b:bool) (r:ref int) (s:ref int)
  requires r |-> 0 ** s |-> 3
  ensures exists* v. r |-> v ** s |-> 3
{
  if (b) { r := 1; } else { () };
  let x = !s;
  assert (pure (x == 3));
  ()
}

(* Unless both branches are unreachable: then it is sound, and accepted. *)
fn both_unreachable_false (b:bool) (r:ref int)
  requires r |-> 0 ** pure False
  ensures r |-> 0
{
  if (b) { () } else { () };
  ()
}
#pop-options

(* One branch's postcondition, unchanged, does not hold of the other. *)
#push-options "--ext pulse:join_fault=then"
[@@expect_failure [19]]
fn writes_differ_then (b:bool) (r:ref int)
  requires r |-> 0
  ensures exists* v. r |-> v
{
  if (b) { r := 1; } else { r := 2; };
  ()
}

(* Were the candidate trusted, this would prove `r |-> 1` in the else
   branch too. *)
[@@expect_failure [19]]
fn writes_differ_then_unsound (b:bool) (r:ref int)
  requires r |-> 0
  ensures r |-> 1
{
  if (b) { r := 1; } else { r := 2; };
  ()
}

(* When the branches agree, a branch's postcondition is correct, and
   accepted. *)
fn writes_same_then (b:bool) (r:ref int)
  requires r |-> 0
  ensures r |-> 1
{
  if (b) { r := 1; } else { r := 1; };
  ()
}
#pop-options

#push-options "--ext pulse:join_fault=else"
[@@expect_failure [19]]
fn writes_differ_else_unsound (b:bool) (r:ref int)
  requires r |-> 0
  ensures r |-> 2
{
  if (b) { r := 1; } else { r := 2; };
  ()
}
#pop-options

(* A fact about the branch hypothesis is provable in both branches, but
   names a variable that is not in scope after the conditional. *)
#push-options "--ext pulse:join_fault=hyp"
[@@expect_failure [76]]
fn writes_differ_hyp (b:bool) (r:ref int)
  requires r |-> 0
  ensures exists* v. r |-> v
{
  if (b) { r := 1; } else { r := 2; };
  ()
}
#pop-options

(* An ill-typed candidate is rejected before the prover sees it. *)
#push-options "--ext pulse:join_fault=ill_typed"
[@@expect_failure [76]]
fn writes_differ_ill_typed (b:bool) (r:ref int)
  requires r |-> 0
  ensures exists* v. r |-> v
{
  if (b) { r := 1; } else { r := 2; };
  ()
}
#pop-options
