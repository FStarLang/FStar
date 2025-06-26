module Bug206

#lang-pulse
open Pulse

fn test (x:nat { x > 0 })
requires emp
ensures emp
{
  ()
}

[@@expect_failure [19]]
fn use_test (x:nat)
requires emp
ensures emp
{
  test x
}
