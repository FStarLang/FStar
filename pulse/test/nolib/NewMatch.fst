module NewMatch

#lang-pulse

open Pulse.Nolib

assume
val foo : [@@@mkey]_:int -> slprop

[@@no_mkeys]
assume
val foo2_nokey
  (k : int)
  (v : int)
  : slprop

assume
val foo2
  ([@@@mkey] k : int)
  (v : int)
  : slprop

fn h ()
  requires foo 3
  ensures  foo 103
{
  admit();
}

fn test0 (x y z : int)
  requires foo x
  requires pure (x == 3)
  ensures  foo 103
{
  rewrite each x as 3;
  h ();
}

[@@expect_failure] // we won't try to ask the SMT if x==3
fn test1 (x y z : int)
  requires foo x
  requires pure (x == 3)
  ensures  foo 103
{
  h ();
}

// reduction still works, of course
fn test2 (x y z : int)
  requires foo (1+2)
  ensures  foo 103
{
  h ();
}

// No keys on foo2_nokey means we try to match occurrences of this predicate,
// and discharge a query.
fn test3 (x y z : int)
  requires foo2_nokey x y
  requires pure (y == z)
  ensures  foo2_nokey x z
{
  ()
}

// But if there are several, then it's ambiguous
[@@expect_failure]
fn test3' (x y z : int)
  requires foo2_nokey 1 z
  requires foo2_nokey x y
  requires pure (y == z)
  ensures foo2_nokey 1 y
  ensures foo2_nokey x z
{
  ()
}
// unless... x has been marked as a key, in which
// case the expectation is that there cannot be two distinct y,z
// such that `foo2 x y` and `foo2 x z` are both true, so we
// commit to proving that `y == z` (i.e. log that as a guard ) and carry on
// checking.
fn test4 (x y z : int)
  requires foo2 x y
  requires pure (y == z)
  ensures  foo2 x z
{
  ()
}

// two key matches is ambiguous, should reject
[@@expect_failure]
fn test5 (x y z w u : int)
  requires foo2 x w
  requires foo2 x y
  requires pure (y == z)
  requires pure (u == w)
  ensures foo2 x z
  ensures foo2 x u
{
  // rewrite foo2 x w as foo2 x u;
  ()
}

// This works since, after rewriting, foo2 x u gets syntactically
// matched and we are left with only foo2 x y |- foo2 x z
fn test6 (x y z w u : int)
  requires foo2 x w
  requires foo2 x y
  requires pure (y == z)
  requires pure (u == w)
  ensures foo2 x z
  ensures foo2 x u
{
  rewrite foo2 x w as foo2 x u;
  ()
}

fn flip2  () (#x #y : int)
  requires foo2 x y
  ensures foo2 y x
{ admit() }

fn test7 (x y z w u : int)
  requires foo2 x y
  ensures  foo2 y x
{
  flip2 ();
  ()
}

[@@expect_failure]
fn test8 (x y z w u : int)
  requires foo2 x y
  requires foo2 w z
  ensures foo2 y x
  ensures foo2 w z
{
  flip2 ();
  ()
}
