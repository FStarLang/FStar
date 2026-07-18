module Bug111

#lang-pulse
open Pulse

[@@expect_failure [114]]
ghost
fn test (x : erased int)
{
  // let x = reveal x;
  match x {
    0 -> {
     ();
    }
    _ -> {
     ();
    }
  }
}
