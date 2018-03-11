module Logic

open FStar.Tactics

assume val phi : Type
assume val psi : Type
assume val  xi: Type

[@plugin]
let tau () : Tac unit =
    let h = implies_intro () in
    right ();
    and_elim (pack (Tv_Var (bv_of_binder h)));
    let h1 = implies_intro () in
    let _ = implies_intro () in
    apply (`FStar.Squash.return_squash);
    exact (pack (Tv_Var (bv_of_binder h1)));
    qed ()

let _ =
    assert_by_tactic (phi /\ xi ==> psi \/ phi) tau
