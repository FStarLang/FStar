module Bug1154

open FStar.Tactics

let a = assert_by_tactic (Bug1154_tactic.app trivial) True