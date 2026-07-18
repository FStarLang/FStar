module Bug110

#lang-pulse
open Pulse

[@@no_mkeys] assume val foo : int -> slprop

(* OK *)
fn test1 (i j : int)
  requires foo i
  requires pure (foo i == foo j)
  ensures  foo j
{
  rewrite foo i as foo j;
}

(* Should fail, we cannot prove i == j *)
[@@expect_failure [19]]
fn test2 (i j : int)
  requires foo i
  requires pure (foo i == foo j)
  ensures  foo j
{
  rewrite each i as j;
}
