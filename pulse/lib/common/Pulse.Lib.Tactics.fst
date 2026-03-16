module Pulse.Lib.Tactics

open FStar.Tactics.V2
open Pulse.Lib.NonInformative

let non_info_tac () : Tac unit =
  match hua (cur_goal ()) with
  | Some (fv, _, [a, _]) -> (
    let nm = implode_qn (inspect_fv fv) in
    if nm = `%non_informative then
    match hua a with
    | Some (fv, _, _) ->
      let nm = implode_qn (inspect_fv fv) in
      if false then
        ()
      else if nm = `%squash then
        apply (`non_informative_squash)
      else if nm = `%unit then
        apply (`non_informative_unit)
      else if nm = `%Ghost.erased then
        apply (`non_informative_erased)
      else if nm = `%prop then
        apply (`non_informative_prop)
      else (
        Tactics.Typeclasses.tcresolve ()
      )
    | _ ->
      fail "non_info_tac: bad call"
  )
  | _ ->
    fail "non_info_tac: bad call"
