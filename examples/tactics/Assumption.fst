module Assumption

open FStar.Tactics

let test1 (x : int {x >= 0}) =
  assert (x >= 0) by assumption

[@expect_failure]
let test2 (x : int {x >= 0}) =
  assert (x >= 1) by assumption

(* I'd love this to work, but I don't see it likely *)
[@expect_failure]
let test3 (x : int {x >= 1}) =
  assert (x >= 0) by assumption
