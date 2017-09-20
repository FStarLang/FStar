module Rename

open FStar.Tactics

assume val phi : Type
assume val psi : Type
assume val xi : Type

assume val p : squash xi

// Sadly, this doesn't work, since what we get as a result
// is the binder's *value* (an embedded alien) and not the
// bound variable pointing to it.
let rename (b : binder) : tactic unit =
    t <-- quote b;
    match inspect t with
    | Tv_Var bb ->
        rename_to b (inspect_bv bb)
    | _ -> fail "not a local variable?"

let l1 (x : bool) (y : int) (z : unit) =
    assert_by_tactic (phi ==> (psi ==> xi))
            (x <-- implies_intro;
             rename_to x "x";;
             y <-- implies_intro;
             rename_to y "y";;
             dump "Test";;
             exact (quote p)
             )
