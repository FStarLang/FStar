module Bug206

#lang-pulse
open Pulse

fn test (x:nat { x > 0 })
{
  ()
}

[@@expect_failure [19]]
fn use_test (x:nat)
{
  test x
}
