module LN

(* Making sure that LN violations don't explode the engine *)

open FStar.Tactics

let badtm () : Tac term =
    pack (Tv_BVar (pack_bv ({ bv_index  = 0;
                              bv_sort   = (`int);
                              bv_ppname = "ouch"; })))
let _ =
    assert_by_tactic True (fun () -> let _ = trytac (fun () -> exact (badtm ())) in trivial ())
