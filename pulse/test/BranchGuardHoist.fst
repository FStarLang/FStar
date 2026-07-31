module BranchGuardHoist

#lang-pulse
open Pulse
module SZ = FStar.SizeT

(* Regression test for a branch return-type hoisting bug.

   The bug is not specific to `while` guards: it affects any `if`/`match` used
   as a value (a `while` guard, or a plain `let`-binding) that is checked with
   no post-condition hint, so its post is inferred. When such an expression's
   boolean result type is refined to mention a branch-local hoisted ANF
   temporary, it used to fail with:

     Error 76 ... universe_of failed:
       top (_: Prims.bool{_ == (FStar.SizeT.v __anf0 < FStar.SizeT.v l2)})
       ... Variable not found: __anf0

   This happens for operators with a refined return type, such as
   `SZ.lt : Pure bool (ensures z == (v x < v y))`: when its stateful argument
   `!j` is hoisted into the branch-local temporary `__anf0`, the result type
   becomes `z:bool{z == (SZ.v __anf0 < SZ.v l2)}`, which escapes its binder.
   The fix (Pulse.Checker.Return, `check_core`) drops refinements that constrain
   the result value (whose formula mentions the refinement binder) -- of any
   shape, not only `z == ...`; the value relation is preserved in the equality
   `result == term` that `comp_return` adds, and payload refinements that do not
   mention the result (e.g. a lemma's `ensures p x`) are kept. *)

(* Stateful read in the else branch (the minimal repro). *)
divergent fn while_szlt_else (i:ref SZ.t) (j:ref SZ.t) (l1:SZ.t) (l2:SZ.t)
  requires i |-> 'vi ** j |-> 'vj
  ensures  exists* vi vj. i |-> vi ** j |-> vj
{
  while ((if (!i `SZ.lt` l1) then true else (!j `SZ.lt` l2)))
    invariant exists* vi vj. i |-> vi ** j |-> vj
  { () }
}

(* Stateful read in the then branch. *)
divergent fn while_szlt_then (i:ref SZ.t) (j:ref SZ.t) (l1:SZ.t) (l2:SZ.t)
  requires i |-> 'vi ** j |-> 'vj
  ensures  exists* vi vj. i |-> vi ** j |-> vj
{
  while ((if (!i `SZ.lt` l1) then (!j `SZ.lt` l2) else false))
    invariant exists* vi vj. i |-> vi ** j |-> vj
  { () }
}

(* Both branches read state. *)
divergent fn while_szlt_both (i:ref SZ.t) (j:ref SZ.t) (l1:SZ.t) (l2:SZ.t)
  requires i |-> 'vi ** j |-> 'vj
  ensures  exists* vi vj. i |-> vi ** j |-> vj
{
  while ((if (!i `SZ.lt` l1) then (!j `SZ.lt` l2) else (!i `SZ.lt` l2)))
    invariant exists* vi vj. i |-> vi ** j |-> vj
  { () }
}

(* No-regression guard: `=` returns plain `bool`, so no refinement leaks; this
   verified before the fix and must keep verifying. *)
divergent fn while_int_else (r:ref int) (s:ref int)
  requires r |-> 'vr ** s |-> 'vs
  ensures  exists* vr vs. r |-> vr ** s |-> vs
{
  while ((if (!r = 0) then true else (!s = 0)))
    invariant exists* vr vs. r |-> vr ** s |-> vs
  { () }
}

(* The same leak outside any `while`: a plain `let`-bound `if`-as-value whose
   else branch reads state. This failed identically before the fix, showing the
   bug is general to `if`/`match`-as-value, not specific to `while` guards. *)
fn let_szlt_else (i:ref SZ.t) (j:ref SZ.t) (l1:SZ.t) (l2:SZ.t)
  requires i |-> 'vi ** j |-> 'vj
  returns b:bool
  ensures  exists* vi vj. i |-> vi ** j |-> vj
{
  let b = (if (!i `SZ.lt` l1) then true else (!j `SZ.lt` l2));
  b
}

(* `let`-bound `if`-as-value with the stateful read in the then branch. *)
fn let_szlt_then (i:ref SZ.t) (j:ref SZ.t) (l1:SZ.t) (l2:SZ.t)
  requires i |-> 'vi ** j |-> 'vj
  returns b:bool
  ensures  exists* vi vj. i |-> vi ** j |-> vj
{
  let b = (if (!i `SZ.lt` l1) then (!j `SZ.lt` l2) else false);
  b
}

(* No-regression guard for the `let`-binding path: `=` returns plain `bool`. *)
fn let_int_else (r:ref int) (s:ref int)
  requires r |-> 'vr ** s |-> 'vs
  returns b:bool
  ensures  exists* vr vs. r |-> vr ** s |-> vs
{
  let b = (if (!r = 0) then true else (!s = 0));
  b
}

(* The leak is not limited to equality refinements. An operand with a *non*-`==`
   refined return type (`bump : x:SZ.t -> Pure SZ.t (ensures fun z -> v z > v x)`)
   yields a branch result type `z:SZ.t{ SZ.v z > SZ.v __anf0 }` that also leaks
   the hoisted temporary. The fix drops any refinement constraining the result
   value (here `SZ.v z > ...`), not only `z == ...`. *)
assume val bump (x:SZ.t) : Pure SZ.t (requires True) (ensures fun z -> SZ.v z > SZ.v x)

fn let_nonEq_refinement (i:ref SZ.t) (j:ref SZ.t) (l1:SZ.t)
  requires i |-> 'vi ** j |-> 'vj
  returns r:SZ.t
  ensures  exists* vi vj. i |-> vi ** j |-> vj
{
  let r = (if (!i `SZ.lt` l1) then 0sz else (bump (!j)));
  r
}
