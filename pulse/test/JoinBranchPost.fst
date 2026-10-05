module JoinBranchPost
#lang-pulse
open Pulse
open Pulse.Lib.Reference

(* An `if` that is not the last statement is checked without a
   postcondition hint: the checker infers each branch's postcondition and
   joins them. These used to leave a `match` on the condition in the joined
   postcondition, which the rest of the function could not use. *)

fn get_any (x:ref int)
  preserves x |-> 'v
  returns v:int
{
  !x
}

let incr (v:int) : int = v + 1

(* The branches store terms over their own hoisted locals. *)
fn join_hoisted (b:bool) (r x:ref int)
  requires r |-> 0 ** x |-> 1
  ensures exists* v. r |-> v ** x |-> 1
{
  if (b) {
    r := incr (get_any x);
  } else {
    r := get_any x;
  };
  ()
}

(* Only one branch stores a term over its hoisted locals; the other stores a
   constant. The cell's value is generalized at the type the head expects. *)
fn join_hoisted_vs_const (b:bool) (r x:ref int)
  requires r |-> 0 ** x |-> 'w
  ensures exists* v. r |-> v ** x |-> 'w
{
  if (b) {
    r := incr (get_any x);
  } else {
    r := 0;
  };
  ()
}

(* As above, at a machine integer type, where the constant's own type is a
   singleton refinement and so cannot serve as the binder's type. *)
fn join_hoisted_vs_const_u32 (b:bool) (r:ref FStar.UInt32.t) (x:ref int)
  requires r |-> 0ul ** x |-> 'w
  ensures exists* v. r |-> v ** x |-> 'w
{
  if (b) {
    let v = get_any x;
    r := (if v > 0 then 1ul else 2ul);
  } else {
    r := 0ul;
  };
  ()
}

let boxed (r:ref int) : slprop = exists* v. r |-> v

[@@pulse_intro]
ghost fn fold_boxed (r:ref int)
  requires r |-> 'v
  ensures boxed r
{
  fold boxed r;
}

fn get_boxed (r:ref int)
  requires boxed r
  returns v:int
  ensures boxed r
{
  unfold boxed r;
  let v = !r;
  fold boxed r;
  v
}

(* The branches end with `r` in different shapes, one unfolded and one
   folded, and the condition is not a variable. *)
fn join_fold_state (b c:bool) (r:ref int) (out:ref int)
  requires boxed r ** out |-> 0
  ensures boxed r ** (exists* v. out |-> v)
{
  unfold boxed r;
  if (b && not c) {
    let v = !r;
    out := v + 1;
  } else {
    fold boxed r;
    let v = get_boxed r;
    out := v;
  };
  ()
}

(* As above, but one branch also writes a cell the other leaves alone. Only
   the part the branches disagree on may come from one branch. Taking all of
   that branch's postcondition would also fix the cell's value. *)
fn join_fold_state_write (b c:bool) (r:ref int) (flag:ref int)
  requires boxed r ** flag |-> 'f
  ensures boxed r ** (exists* v. flag |-> v)
{
  unfold boxed r;
  if (b && not c) {
    flag := 1;
  } else {
    fold boxed r;
  };
  ()
}

(* Neither branch's state is that of the other. *)
[@@expect_failure]
fn join_no_common_state (b:bool) (r:ref int)
  requires r |-> 0
  ensures r |-> 1
{
  if (b) { r := 1; } else { () };
  ()
}

(* A branch's path condition does not survive the join. *)
[@@expect_failure]
fn join_no_path_condition (b:bool) (r:ref int)
  requires r |-> 0
  ensures r |-> 0 ** pure (b == false)
{
  if (b) { () } else { () };
  ()
}

[@@expect_failure]
fn join_no_path_condition_then (b:bool) (r:ref int)
  requires r |-> 0
  ensures r |-> 0 ** pure (b == true)
{
  if (b) { () } else { () };
  ()
}
