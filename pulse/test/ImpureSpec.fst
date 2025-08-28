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

ghost fn array_val #t (r: array t) #p (#v: Seq.seq t)
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
  while ((!y > !x))
    invariant (live y) ** pure (!y >= !x /\ !y <= old (!y))
    // elaborates to: exists* vy. (y |-> vy) ** pure (vy >= 10 /\ vy <= 20)
  {
    y := !y - 1;
  };
  assert pure (10 <= !y /\ !y <= 20);
}

fn rec test7 (r: ref int)
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
  ensures pure (w == old(!(old(!x))))
{
  !(!x);
}