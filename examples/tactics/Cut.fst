module Cut

open FStar.Tactics

assume val phi : Type
assume val psi : Type

assume val p1 : psi
assume val p2 : psi -> squash phi

let _ =
    assert_by_tactic phi
        (psi' <-- quote psi;
         tcut psi';;
         flip;;
         exact (quote p1);; // TODO: kinda pointless example
         apply (quote p2);;
         exact (quote p1))
