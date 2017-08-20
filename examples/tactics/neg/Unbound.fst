module Unbound

open FStar.Tactics

let tau : tactic unit =
    split;;
    x <-- implies_intro;
    squash_intro;; exact (return (pack (Tv_Var x)));;
    // `x` is unbound in this environment, we should fail
    // (if it succeeds: is the use_bv_sorts flag on? it should be off)
    squash_intro;; exact (return (pack (Tv_Var x)))

let _ = assert_by_tactic tau ((False ==> False) /\ False)
