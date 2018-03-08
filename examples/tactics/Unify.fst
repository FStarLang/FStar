module Unify

open FStar.Tactics

let h : int =
    synth_by_tactic (fun () ->
        let l = fresh_uvar None in // None: we don't provide a type
        let r = fresh_uvar None in
        apply (`op_Addition);
        exact l;
        exact r;
        let ocho = `8 in
        let _ = unify r ocho in
        let _ = unify l r in
        ()
    )

let _ = assert (h == 16)
