module Logic

open FStar.Tactics

assume val phi : Type
assume val psi : Type
assume val  xi: Type

let tau : tactic unit =
    h <-- implies_intro;
    right;;
    dump1 "GG 1";;
    and_elim (pack (Tv_Var h));;
    dump1 "GG 2";;
    h1 <-- implies_intro;
    implies_intro;;
    dump1 "GG 3";;
    apply (quote (FStar.Squash.return_squash));;
    exact (return (pack (Tv_Var h1)));;
    dump1 "GG 4";;
    qed

let _ =
    assert_by_tactic tau (phi /\ xi ==> psi \/ phi)
