module ShortCircuitStatefulBool

#lang-pulse
open Pulse

(* Helpers whose state update makes eager evaluation of a skipped operand visible. *)
fn tick_true (n: ref int)
  requires n |-> 'v
  returns b: bool
  ensures n |-> ('v + 1) ** pure (b)
{
  n := !n + 1;
  true
}

fn stateful_and_skips_rhs (flag: ref bool) (n: ref int)
  requires flag |-> false ** n |-> 0
  returns b: bool
  ensures flag |-> false ** n |-> 0 ** pure (b == false)
{
  (!flag) && tick_true n
}

fn stateful_and_runs_rhs (flag: ref bool) (n: ref int)
  requires flag |-> true ** n |-> 0
  returns b: bool
  ensures flag |-> true ** n |-> 1 ** pure (b)
{
  (!flag) && tick_true n
}

fn stateful_or_skips_rhs (flag: ref bool) (n: ref int)
  requires flag |-> true ** n |-> 0
  returns b: bool
  ensures flag |-> true ** n |-> 0 ** pure (b)
{
  (!flag) || tick_true n
}

fn stateful_or_runs_rhs (flag: ref bool) (n: ref int)
  requires flag |-> false ** n |-> 0
  returns b: bool
  ensures flag |-> false ** n |-> 1 ** pure (b)
{
  (!flag) || tick_true n
}

fn nested_stateful_and_or (a: ref bool) (b: ref bool) (n: ref int)
  requires a |-> false ** b |-> false ** n |-> 0
  returns r: bool
  ensures a |-> false ** b |-> false ** n |-> 0 ** pure (r == false)
{
  (!a) && ((!b) || tick_true n)
}

fn nested_stateful_or_and (a: ref bool) (b: ref bool) (n: ref int)
  requires a |-> true ** b |-> true ** n |-> 0
  returns r: bool
  ensures a |-> true ** b |-> true ** n |-> 0 ** pure (r)
{
  (!a) || ((!b) && tick_true n)
}

(* Equivalent expression-position conditionals.  The condition is not a bare
   variable after hoisting the read; branch joining must still infer a usable
   postcondition and simplify it under the branch hypothesis. *)
fn explicit_if_expr_then (i: ref int) (n: ref int)
  requires i |-> 1 ** n |-> 0
  returns b: bool
  ensures i |-> 1 ** n |-> 1 ** pure (b)
{
  let b = (if (!i = 1) then tick_true n else false);
  b
}

fn explicit_if_expr_else (i: ref int) (n: ref int)
  requires i |-> 1 ** n |-> 0
  returns b: bool
  ensures i |-> 1 ** n |-> 0 ** pure (b == false)
{
  let b = (if (!i = 0) then tick_true n else false);
  b
}

(* The while checker still cannot infer the postcondition for a guard whose
   boolean result is tied to a stateful short-circuit branch. *)
[@@expect_failure]
fn while_guard_and_short_circuits (i: ref int) (n: ref int)
  requires i |-> 1 ** n |-> 0
  ensures i |-> 1 ** n |-> 0
{
  while ((!i = 0) && tick_true n)
    invariant i |-> 1 ** n |-> 0
  { () }
}

fn pure_operands_no_regression (x: bool) (y: bool)
  returns r: bool
  ensures pure (r == ((x && y) || (x || y)))
{
  let a = x && y;
  let b = x || y;
  a || b
}
