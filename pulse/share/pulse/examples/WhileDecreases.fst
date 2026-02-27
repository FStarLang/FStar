module WhileDecreases
#lang-pulse
open Pulse.Lib.Pervasives

fn test (x:ref nat)
requires live x
ensures x |-> (0<:nat)
{
  while (!x > 0)
  invariant live x
  decreases (!x)
  {
    x := !x - 1;
  }
}

fn test2 (x:ref nat)
requires live x
ensures x |-> (0<:nat)
{
  while (!x > 0)
  invariant exists* y. pts_to x y
  decreases (!x)
  {
    x := !x - 1;
  }
}

fn test3 (x:ref nat)
requires live x
ensures x |-> (0<:nat)
{
  while (!x > 0)
  invariant exists* y. pts_to x y
  decreases reveal (value_of x)
  {
    x := !x - 1;
  }
}

let rec lex_rec (x y:nat)
: Tot unit (decreases %[x;y])
= if x = 0 && y = 0 then ()
  else if x > 0 then lex_rec (x - 1) y
  else lex_rec x (y - 1)

[@@expect_failure]
fn lex (x y:ref nat)
requires live x ** live y
ensures x |-> (0<:nat) ** y |-> (0<:nat)
{
  while (!x > 0 || !y > 0)
  invariant live x
  invariant live y
  decreases %[(!x); (!y)]
  {
    if (!x = 0) { y := !y - 1; }
    else { x := !x - 1; }
  }
}