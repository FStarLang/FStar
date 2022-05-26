module Test

open FStar.Meta.Tc.Effect
open FStar.Meta.Tc.Builtins

open FStar.Tactics

let tau () : Tac unit =
  let en = cur_env () in
  let token = check_prop_validity en (`True) in
  ()

let test () =
  assert (hasEq nat) by (tau ())
