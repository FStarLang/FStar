module Clear

open FStar.Tactics

assume val phi : Type
assume val psi : Type
assume val xi : Type

assume val p : squash xi

let l (x : bool) (y : int) (z : unit) =
    assert_by_tactic (phi ==> (psi ==> xi))
            (implies_intro;;
             clear;;
             implies_intro;;
             clear;;
             exact (quote p)
             )
