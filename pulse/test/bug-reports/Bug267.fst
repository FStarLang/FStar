module Bug267

#lang-pulse
open Pulse
open FStar.Mul

(* Complains that 'v is ghost, good. *)
[@@expect_failure [228]]
fn value_of (#a:Type) (r:ref a)
  requires pts_to r 'v
  returns v:a
  ensures pts_to r 'v ** pure (v == 'v)
{
    'v
}

fn add (r : ref int) (v : int)
  requires pts_to r 'v0
  ensures  pts_to r (v + 'v0)
{
  let v0 = !r;
  r := v0 + v
}

(* Complains in !i: expected int got stt .... Could be better. *)
[@@expect_failure [12]]
fn four_fail ()
  requires emp
  returns i:int
  ensures pure (i == 4)
{
    let mut i = 1;
    add i (!i);
    add i (!i);
    !i
}

[@@expect_failure [19]]
fn multiply_by_repeated_addition (x y:nat)
    requires emp
    returns z:nat
    ensures pure (z == x * y)
{
    let mut ctr = 0;
    let mut acc : int = 0;
    while (
        let c = !ctr;
        (c < x)
    )
    invariant b.
    exists* (c a : int).
        pts_to ctr c **
        Pulse.Lib.Reference.pts_to acc a **
        pure (//0 <= c /\
              c <= x /\
              a == (c * y) /\
              b == (c < x))
    {
        let a = !acc;
        acc := a + y;
        let c = !ctr;
        ctr := c + 1;
    };
    !acc
}

[@@expect_failure [12]]
fn foo (n: nat) requires pure (n >= 42) ensures emp {
  assert (n >= 1);
}

