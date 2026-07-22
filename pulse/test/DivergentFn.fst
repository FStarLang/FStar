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

(* Regression for #4366: calling a `divergent fn` from a branch of an `if` that
   is itself in bind position (i.e. not the tail) inside a `divergent fn`. The
   `if`'s postcondition is inferred, and the divergent branch must make the whole
   conditional divergent instead of failing to compose against `stt`. *)
divergent fn diverge ()
requires emp
ensures emp
{
    while (true)
    invariant emp
    { () }
}

divergent fn if_then_diverges () {
    if true { diverge () };
    ()
}

divergent fn if_else_diverges () {
    if true { () } else { diverge () };
    ()
}

divergent fn nested_if_diverges () {
    if true { if true { diverge () } };
    ()
}

(* The same `if` inside a plain `fn` is still rejected: a divergent branch cannot
   be composed at `stt`. *)
[@@expect_failure [228]]
fn if_diverges_bad () {
    if true { diverge () };
    ()
}
