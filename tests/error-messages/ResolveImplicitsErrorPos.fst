module ResolveImplicitsErrorPos

open FStar.Tactics.V2

let tag : unit = ()

[@@ resolve_implicits; tag]
let tau () : Tac unit =
  fail "oops"

let f (#[@@@defer_to tag] x:int) : int = x

[@@expect_failure]
let test () =
  let x = f in
  x + 1
