module DivergentFn
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
#lang-pulse

(* A `while` loop with no `decreases` measure is accepted inside a
   `divergent fn`: such a function has type `stt_div`. *)
divergent fn spin (x:ref nat)
requires R.pts_to x 'v
ensures  R.pts_to x 0
{
    while (
        let n = !x;
        if (n = 0) { false }
        else { x := n + 1; true }
    )
    invariant exists* v. R.pts_to x v
    { () }
}

(* The SAME body in a plain `fn` is rejected: a measure-free `while` makes the
   body divergent, but a plain `fn` must be terminating (`stt`). *)
[@@expect_failure [228]]
fn spin_bad (x:ref nat)
requires R.pts_to x 'v
ensures  R.pts_to x 0
{
    while (
        let n = !x;
        if (n = 0) { false }
        else { x := n + 1; true }
    )
    invariant exists* v. R.pts_to x v
    { () }
}

(* A terminating `while` with a `decreases` measure stays at `stt` and may be a
   plain `fn`. *)
fn count_down ()
requires emp
ensures  emp
{
    let mut i = 0;
    while (!i < 10)
    invariant live i
    invariant pure (!i <= 10)
    decreases (Prims.op_Subtraction 10 (!i))
    { i := !i + 1; }
}

(* Divergence is infectious and terminating code lifts silently: a
   `divergent fn` may call a plain (terminating) `fn`. *)
fn helper (x:ref nat)
requires R.pts_to x 'v
ensures  R.pts_to x 'v
{ () }

divergent fn calls_terminating (x:ref nat)
requires R.pts_to x 'v
ensures  R.pts_to x 'v
{
    helper x;
    ()
}
