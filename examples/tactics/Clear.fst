module Clear

open FStar.Tactics

assume val phi : Type
assume val psi : Type
assume val xi : Type

let l (x : bool) (y : int) (z : unit) =
    assert_by_tactic
            (dump "HUH?";;
             implies_intro;;
             dump "GG 1";;
             clear;;
             dump "GG 2";;
             implies_intro;;
             dump "GG 3";;
             clear;;
             dump "GG 4"
             ) (phi ==> (psi ==> xi))
