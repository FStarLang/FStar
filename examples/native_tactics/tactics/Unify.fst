module Unify

open FStar.Tactics

[@plugin]
let tau =
  fun () ->
        let l = fresh_uvar None in // None: we don't provide a type
        let r = fresh_uvar None in
        apply (`op_Addition);
        exact l;
        exact r;
        let ocho = `8 in
        let _ = unify r ocho in
        let _ = unify l r in
        ()

let h : int = synth_by_tactic tau

let _ = assert (h == 16)
