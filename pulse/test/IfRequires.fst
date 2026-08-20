(* Tests for the `requires`/`ensures` annotations on conditionals.

   `if b ensures q { .. }` fixes the postcondition of the conditional to `q`,
   and so `q` must describe the *whole* context. Adding a `requires p` restricts
   the annotation to the part of the context described by `p`: the rest of the
   context is framed out and silently added back to `q`. *)
module IfRequires
open Pulse.Lib.Pervasives
#lang-pulse

(* Without a `requires`, the `ensures` must mention `x` even though the
   conditional does not touch it. *)
fn ensures_only ()
requires emp
ensures emp
{
  let mut x = 6;
  let mut y = 7;
  if (!x < !y)
    ensures (x |-> 6) ** (y |-> 42)
  {
    y := !x + 36;
  } else {
    y := 42;
  };
  ()
}

(* With a `requires`, only `y` needs to be mentioned; `x |-> 6` is framed out
   and added back to the postcondition. *)
fn requires_frames_the_rest ()
requires emp
ensures emp
{
  let mut x = 6;
  let mut y = 7;
  if (!x < !y)
    requires live y
    ensures y |-> 42
  {
    y := !x + 36;
  } else {
    y := 42;
  };
  (* the framed-out `x |-> 6` is still in the context *)
  let v = !x;
  assert (pure (v == 6));
  ()
}

(* The framed-out part of the context is still available inside the branches. *)
fn frame_is_readable_in_branches ()
requires emp
ensures emp
{
  let mut x = 6;
  let mut y = 7;
  if (!x < !y)
    requires live y
    ensures y |-> 42
  {
    let v = !x;
    assert (pure (v == 6));
    y := v + 36;
  } else {
    y := 42;
  };
  ()
}

(* A `requires` that does not hold in the context is an error. *)
[@@expect_failure]
fn requires_not_provable (r:ref int)
requires emp
ensures emp
{
  if (true)
    requires live r
    ensures live r
  { () };
  ()
}

(* A `requires` must be accompanied by an `ensures`. *)
[@@expect_failure [168]]
fn requires_without_ensures ()
requires emp
ensures emp
{
  let mut y = 7;
  if (!y = 7)
    requires live y
  {
    y := 42;
  };
  ()
}

(* An annotated conditional with a stateful condition. *)
fn stateful_condition (r:ref int)
requires pts_to r 'v
ensures  pts_to r 'v
{
  let mut y = 7;
  if (!r = 0)
    requires live y
    ensures  live y
  {
    y := 42;
  } else {
    y := 0;
  };
  ()
}

(* Annotations on the branches of an `else if` cascade. *)
fn else_if_cascade (b1 b2:bool)
requires emp
ensures emp
{
  let mut x = 0;
  let mut y = 1;
  if (b1)
    requires live y
    ensures  y |-> 2
  {
    y := 2;
  } else if (b2) {
    y := 2;
  } else {
    y := 2;
  };
  let v = !x;
  assert (pure (v == 0));
  ()
}

(* The postcondition established by the annotation is what the continuation
   sees, whether or not a `requires` is given. *)
fn post_is_visible_to_continuation ()
requires emp
ensures emp
{
  let mut y = 7;
  if (true)
    requires live y
    ensures  y |-> 42
  {
    y := 42;
  } else {
    y := 42;
  };
  let v = !y;
  assert (pure (v == 42));
  ()
}

(* The `requires` may mention existentials; they are eliminated when it is
   proven against the context, and re-introduced by the `ensures`. *)
fn existential_annotations (x y:ref int)
requires pts_to x 'vx ** pts_to y 'vy
ensures  pts_to x 'vx ** (exists* v. pts_to y v)
{
  if (true)
    requires exists* v. pts_to y v
    ensures  exists* v. pts_to y v ** pure (v >= 0)
  {
    y := 0;
  } else {
    y := 1;
  };
  ()
}

(* An annotated conditional in the body of a loop. *)
fn annotated_if_in_loop (x y:ref int)
requires pts_to x 'vx ** pts_to y 'vy
ensures  exists* a b. pts_to x a ** pts_to y b
{
  let mut i = 0;
  while (!i < 10)
  invariant exists* a b v. pts_to x a ** pts_to y b ** pts_to i v ** pure (v <= 10)
  decreases (10 - !i)
  {
    if (!i % 2 = 0)
      requires exists* b. pts_to y b
      ensures  exists* b. pts_to y b
    {
      y := 1;
    } else {
      y := 2;
    };
    i := !i + 1;
  };
  ()
}
