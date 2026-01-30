module Bug267

#lang-pulse
open Pulse
open FStar.Mul

(* Complains that 'v is ghost, good. *)
[@@expect_failure [228]]
fn value_of u#a (#a:Type u#a) (r:ref a)
  requires pts_to r 'v
  returns v:a
  ensures pts_to r 'v
  ensures pure (v == 'v)
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
    invariant
    exists* (c a : int).
        pts_to ctr c **
        Pulse.Lib.Reference.pts_to acc a **
        pure (//0 <= c /\
              c <= x /\
              a == (c * y))
    {
        let a = !acc;
        acc := a + y;
        let c = !ctr;
        ctr := c + 1;
    };
    !acc
}

[@@expect_failure [228]]
fn foo (n: nat) requires pure (n >= 42) ensures emp {
  assert (n >= 1); //misses a pure
}

