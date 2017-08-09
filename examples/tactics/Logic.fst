module Logic

open FStar.Tactics

assume val phi : Type
assume val psi : Type
assume val  xi: Type

let tau : tactic unit =
    h <-- implies_intro;
    right;;
    and_elim (pack (Tv_Var h));;
    h1 <-- implies_intro;
    implies_intro;;
    apply (quote (FStar.Squash.return_squash));;
    exact (return (pack (Tv_Var h1)));;
    qed

let _ =
    assert_by_tactic (phi /\ xi ==> psi \/ phi) tau
