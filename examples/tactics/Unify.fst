module Unify

open FStar.Tactics

let h : int =
    synth_by_tactic (fun () ->
        let l = fresh_uvar None in // None: we don't provide a type
        let r = fresh_uvar None in
        let e = cur_env () in
        apply (`op_Addition);
        exact l;
        exact r;
        let ocho = `8 in
        let _ = unify_env e r ocho in
        let _ = unify_env e l r in
        ()
    )

let _ = assert (h == 16)


(* Types do not unify, so this fails *)
val x : squash False
[@ (Pervasives.fail [228])]
let x = assert_by_tactic False
            (fun () -> let w = cur_witness () in
                       let e = cur_env () in
                       dismiss ();
                       if unify_env e w (`())
                       then ()
                       else fail "no")
