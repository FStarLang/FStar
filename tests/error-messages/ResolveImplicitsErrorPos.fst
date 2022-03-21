module ResolveImplicitsErrorPos

open FStar.Tactics

let tag : unit = ()

[@@ resolve_implicits; tag]
let tau () : Tac unit =
  fail "oops"

let f (#[@@@tag] x:int) : int = x

[@@expect_failure]
let test () =
  let x = f in
  x + 1
