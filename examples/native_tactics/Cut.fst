module Cut

open FStar.Tactics

assume val phi : Type
assume val psi : Type

assume val p1 : psi
assume val p2 : psi -> squash phi

[@plugin]
let tau =
        (fun () ->
             let psi' = `psi in
             let _ = tcut psi' in
             flip ();
             exact (`p1); // TODO: kinda pointless example
             apply (`p2);
             exact (`p1))

let _ =
    assert_by_tactic phi tau

