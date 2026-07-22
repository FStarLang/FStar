module ImpureSpec
open Pulse
open Pulse.Lib.Trade
open Pulse.Lib.WithPure
#lang-pulse

fn test1 () {
  let mut x = 2;
  let mut y = x;
  assert pure (!(!y) == 2);
}

fn test2 (r: ref int)
  preserves r |-> 'v
  requires pure (!r > 10)
{
  assert pure (!r > 5);
}

fn test3 (r: ref int)
  preserves live r
  requires pure (!r > 10)
  ensures pure (!r > 15)
{
  r := !r + 10;
  assert (exists* v'. r |-> v') ** pure (!r > 17); // refers to v' from the exists!
}

ghost fn array_val u#a (#t: Type u#a) (r: array t) #p (#v: Seq.seq t)
  preserves r |-> Frac p v
  returns x: Seq.seq t
  ensures rewrites_to x v
{ v }

fn test4 (r: array int)
  preserves live r
  preserves with_pure (Seq.length (array_val r) == 10)
  requires pure (forall i. SizeT.v i < Seq.length (array_val r) ==> r.(i) == 0)
  ensures pure (r.(1sz) == 42)
{
  r.(1sz) <- 42
}

fn test5 (r: ref int)
  preserves live r
  ensures pure (!r > old (!r))
{
  r := (!r) + 1
}

fn test6 () {
  let mut x = 10;
  let mut y = 20;
  while (!y > !x)
    invariant (live y) ** pure (!y >= !x /\ !y <= old (!y))
    decreases (!y - !x)
    // elaborates to: exists* vy. (y |-> vy) ** pure (vy >= 10 /\ vy <= 20)
  {
    y := !y - 1;
  };
  assert pure (10 <= !y /\ !y <= 20);
}

divergent fn rec test7 (r: ref int)
  preserves live r
  ensures pure (!r <= old !r)
{
  if (!r > 1) {
    r := !r - 1;
    test7 r
  }
}

fn test8a (r: ref int)
  preserves live r
  requires with_pure (!r > 10)
{ () }
fn test8b (r: ref int)
  preserves live r
  requires with_pure (!r > 10)
{ test8a r } // make sure we can call functions with with_pure pres.

[@@pulse_unfold]
let nested_pts_to (x: ref (ref int)) (y: int) =
  exists* (z: ref int). (x |-> z) ** (z |-> y)

[@@pulse_eager_unfold]
let nested_live (x: ref (ref int)) =
  exists* y. nested_pts_to x y

fn test9 (x: ref (ref int))
  preserves nested_live x
  ensures pure (!(!x) == 10)
{
  !x := 10;
}

fn test10 (x: bool)
  returns y: _
  ensures pure (x == y)
{ x }

fn test11 (x:ref (ref int))
  preserves nested_live x
  returns w:_
  ensures pure (w == old(! !x))
{
  !(!x);
}

fn test12 ()
{
  let mut x = 2;
  rewrite x |-> !x as x |-> (0 + !x * 1);
}

let p13 (x: ref int) = live x
fn test13 ()
{
  let mut x = 42;
  let mut y = x;
  fold p13 (!y);
  unfold p13 (!y);
}

fn test14 ()
{
  let mut x = 42;
  assert live x ** pure (!x == 42);
  rewrite each !x as 42;
}

let max_spec (x y: int) = if x < y then y else x

// A non-tail `if` annotated with a postcondition that uses impure spec
// syntax (the `!result` selector). The annotation must be purified before
// being used as the post hint.
fn test15_if #p #q (x y: ref int)
  preserves pts_to x #p 'vx
  requires pts_to y #q 'vy
  returns n: int
  ensures pts_to y #q 'vy ** pure (n == max_spec 'vx 'vy)
{
  let mut result = 0;
  let vx = !x;
  let vy = !y;
  if (vx > vy)
  ensures
    pts_to x #p 'vx **
    pts_to y #q 'vy **
    (exists* r. pts_to result r) **
    pure (!result == max_spec 'vx 'vy)
  {
    result := vx;
  }
  else
  {
    result := vy;
  };
  !result;
}

// Same as test15_if, but for a non-tail `match`.
fn test16_match #p #q (x y: ref int)
  preserves pts_to x #p 'vx
  requires pts_to y #q 'vy
  returns n: int
  ensures pts_to y #q 'vy ** pure (n == max_spec 'vx 'vy)
{
  let mut result = 0;
  let vx = !x;
  let vy = !y;
  match (vx > vy)
  ensures
    pts_to x #p 'vx **
    pts_to y #q 'vy **
    (exists* r. pts_to result r) **
    pure (!result == max_spec 'vx 'vy)
  {
    true -> { result := vx; }
    false -> { result := vy; }
  };
  !result;
}

// Regression tests for issue #4347: spec purification must descend into the
// direct slprop-typed arguments of combinators, so that stateful reads
// (e.g. `!r`) inside a combinator argument can see sibling resources.
// Predicate-abstraction (function-typed) arguments are intentionally not
// descended into (see Pulse.Checker.ImpureSpec.purify_args).

let id_wrap (p: slprop) : slprop = p
let nonneg (v: int) : slprop = pure (v >= 0)

// Direct slprop argument: `!r` is resolved using the `pts_to r` sibling that
// lives inside the same combinator argument.
fn test17_comb_direct ()
  returns r : (ref int)
  ensures exists* (v: int). id_wrap (pts_to r v ** nonneg (!r))
{ admit () }

// The existential introduced while purifying `live x` must stay *inside* the
// combinator argument: `id_wrap (live x ** pure (!x >= 0))` purifies to
// `id_wrap (exists* y. pts_to x y ** pure (y >= 0))`. With no outer resource
// for `x`, the `!x` must be resolved by the `live x` inside the argument.
fn test18_comb_exists_inside (x: ref int)
  ensures id_wrap (live x ** pure (!x >= 0))
{ admit () }
