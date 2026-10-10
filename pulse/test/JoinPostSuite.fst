module JoinPostSuite
#lang-pulse
open Pulse
open Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module Box = Pulse.Lib.Box
module A = Pulse.Lib.Array

(* Inferred postconditions of an `if` that is not the last statement of a
   block (so checked without a postcondition hint). The positive tests check
   that what the branches agree on, and what one branch establishes under its
   own condition, is usable after the join. The negative tests check that
   nothing true of only one branch survives it. *)

(*** Positive ***)

(* A frame no branch mentions survives, whatever the branches do. *)
fn frame_untouched (b:bool) (r s:ref int) (bx:Box.box bool)
  requires r |-> 0 ** s |-> 7 ** Box.pts_to bx true
  ensures exists* v. r |-> v ** s |-> 7 ** Box.pts_to bx true
{
  if (b) { r := 1; } else { r := 2; };
  let x = !s;
  let y = Box.(!bx);
  assert (pure (x == 7 /\ y == true));
  ()
}

(* A cell written in both branches can be used, and written again. *)
fn written_both_then_write (b:bool) (r:ref int)
  requires r |-> 0
  ensures r |-> 5
{
  if (b) { r := 1; } else { r := 2; };
  let v = !r;
  r := 5;
  ()
}

(* The value of such a cell is known to be one of the two. *)
fn written_both_value (b:bool) (r:ref int)
  requires r |-> 0
  ensures exists* v. r |-> v ** pure (v == 1 \/ v == 2)
{
  if (b) { r := 1; } else { r := 2; };
  ()
}

(* What each branch proves, under its own condition. *)
fn written_both_guarded (b:bool) (r:ref int)
  requires r |-> 0
  ensures r |-> 0
{
  if (b) { r := 1; } else { r := 2; };
  let v = !r;
  assert (pure (b ==> v == 1));
  assert (pure (not b ==> v == 2));
  r := 0;
}

(* Different cells written in each branch. *)
fn different_cells (b:bool) (r s:ref int)
  requires r |-> 0 ** s |-> 0
  ensures exists* v w. r |-> v ** s |-> w
{
  if (b) { r := 1; } else { s := 1; };
  r := 3;
  s := 4;
}

(* The result of the conditional. *)
fn result_value (b:bool) (r:ref int)
  requires r |-> 0
  ensures r |-> 0
{
  let x = if (b) { let v = !r; v + 1 } else { 2 };
  assert (pure (x == 1 \/ x == 2));
  ()
}

(* Each branch binds a witness and a fact about it. *)
fn witness_fact (b:bool) (r:ref int)
  requires r |-> 0
  ensures exists* v. r |-> v ** pure (v > 0)
{
  if (b) { r := 1; } else { r := 2; };
  let v = !r;
  assert (pure (v > 0));
  ()
}

(* The condition is not a variable. *)
fn condition_expression (x y:int) (r:ref int)
  requires r |-> 0
  ensures exists* v. r |-> v
{
  if (x > y && y > 0) { r := x; } else { r := y; };
  let v = !r;
  r := v + 1;
}

(* A conditional nested in a branch of another. *)
fn nested (b c:bool) (r s:ref int)
  requires r |-> 0 ** s |-> 0
  ensures exists* v w. r |-> v ** s |-> w
{
  if (b) {
    if (c) { r := 1; } else { s := 1; };
    r := 2;
  } else {
    s := 2;
  };
  r := 3;
  s := 4;
}

(* Two conditionals in sequence on the same variable. *)
fn sequenced (b:bool) (r:ref int)
  requires r |-> 0
  ensures exists* v. r |-> v
{
  if (b) { r := 1; } else { () };
  if (b) { r := 2; } else { r := 3; };
  let v = !r;
  assert (pure (v == 2 \/ v == 3));
  ()
}

(* A branch allocates and frees a local of its own. *)
fn local_in_branch (b:bool) (r:ref int)
  requires r |-> 0
  ensures exists* v. r |-> v
{
  if (b) {
    let bx = Box.alloc 5;
    Box.(bx := 6);
    let v = Box.(!bx);
    Box.free bx;
    r := v - 1;
  } else {
    let bx = Box.alloc 6;
    let v = Box.(!bx);
    Box.free bx;
    r := v;
  };
  let v = !r;
  assert (pure (v == 5 \/ v == 6));
  ()
}

(* Ghost state. *)
fn ghost_cells (b:bool) (r:GR.ref int)
  requires GR.pts_to r 0
  ensures exists* v. GR.pts_to r v ** pure (v >= 0)
{
  if (b) { GR.(r := 1); } else { GR.(r := 2); };
  ()
}

(* An array, with a fact about its length that both branches keep. *)
fn array_both (b:bool) (a:A.array int) (#s:erased (Seq.seq int))
  requires A.pts_to a s ** pure (Seq.length s == 2)
  ensures exists* s'. A.pts_to a s'
{
  A.pts_to_len a;
  if (b) { A.(a.(0sz) <- 1); } else { A.(a.(1sz) <- 2); };
  A.pts_to_len a;
  A.(a.(1sz) <- 3);
}

(* In a loop body. *)
fn in_loop (r:ref int) (n:ref int)
  requires r |-> 0 ** n |-> 3
  ensures exists* v k. r |-> v ** n |-> k
{
  while (!n > 0)
    invariant live r
    invariant live n
    invariant pure (!n >= 0)
    decreases (!n)
  {
    let k = !n;
    if (k % 2 = 0) { r := 1; } else { r := 2; };
    n := k - 1;
  };
}

(* One branch cannot be reached: the other's state is the join. *)
fn one_unreachable (b:bool) (r:ref int)
  requires r |-> 0 ** pure (b == true)
  ensures r |-> 1
{
  if (b) { r := 1; } else { unreachable () };
  ()
}

(*** Negative ***)

(* A value written in one branch only. *)
[@@expect_failure [19]]
fn neg_value_from_then (b:bool) (r:ref int)
  requires r |-> 0
  ensures r |-> 1
{
  if (b) { r := 1; } else { r := 2; };
  ()
}

[@@expect_failure [19]]
fn neg_value_from_else (b:bool) (r:ref int)
  requires r |-> 0
  ensures r |-> 2
{
  if (b) { r := 1; } else { r := 2; };
  ()
}

(* A fact established in one branch only. *)
[@@expect_failure [19]]
fn neg_fact_from_branch (b:bool) (r:ref int)
  requires r |-> 0
  ensures r |-> 0
{
  if (b) { r := 1; } else { r := 2; };
  let v = !r;
  assert (pure (v == 1));
  r := 0;
}

(* The result of one branch. *)
[@@expect_failure [19]]
fn neg_result_value (b:bool)
  requires emp
  ensures emp
{
  let x = if (b) { 1 } else { 2 };
  assert (pure (x == 1));
  ()
}

(* Two cells written to the same value in one branch only cannot be
   claimed equal after the join. *)
[@@expect_failure [19]]
fn neg_correlated_cells (b:bool) (r s:ref int)
  requires r |-> 0 ** s |-> 0
  ensures exists* v. r |-> v ** s |-> v
{
  if (b) { r := 1; s := 1; } else { r := 1; s := 2; };
  ()
}

(* A cell freed in one branch only is not owned after the join. *)
[@@expect_failure [228]]
fn neg_freed_in_branch (b:bool) (bx:Box.box int)
  requires Box.pts_to bx 0
  ensures emp
{
  if (b) { Box.free bx; } else { () };
  ()
}

[@@expect_failure [228]]
fn neg_use_after_branch_free (b:bool) (bx:Box.box int)
  requires Box.pts_to bx 0
  ensures exists* v. Box.pts_to bx v
{
  if (b) { Box.free bx; } else { () };
  Box.(bx := 1);
}

(* A cell allocated in one branch only. *)
[@@expect_failure [228]]
fn neg_alloc_in_branch (b:bool)
  requires emp
  ensures emp
{
  if (b) { let bx = Box.alloc 0; () } else { () };
  ()
}

(* A ghost cell's value from one branch. *)
[@@expect_failure [19]]
fn neg_ghost_value (b:bool) (r:GR.ref int)
  requires GR.pts_to r 0
  ensures GR.pts_to r 1
{
  if (b) { GR.(r := 1); } else { GR.(r := 2); };
  ()
}

(* A witness from one branch, against a predicate from the other. *)
assume val pred (v:int) : slprop

ghost fn set_pred (r:ref int) (v:int)
  requires exists* w. r |-> w ** pred w
  ensures r |-> v ** pred v
{
  admit ()
}

fn linked_witness (b:bool) (r:ref int)
  requires r |-> 0 ** pred 0
  ensures exists* v. r |-> v ** pred v
{
  if (b) { set_pred r 1; } else { set_pred r 2; };
  ()
}

[@@expect_failure [19]]
fn neg_linked_witness (b:bool) (r:ref int)
  requires r |-> 0 ** pred 0
  ensures exists* v w. r |-> v ** pred w ** pure (v =!= w)
{
  if (b) { set_pred r 1; } else { set_pred r 2; };
  ()
}
