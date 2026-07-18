module FStar.Tactics.BreakVC

open FStar.Tactics.V2

let mono_lem () : Lemma (tac_wp_monotonic #unit break_wp') =
  ()

#push-options "--no_tactics" // don't process `with_tactic` markers

let aux (p : unit -> prop)
: Lemma (break_wp p ==> tac_return_wp () p)
= calc (==>) {
    break_wp p;
    == {}
    spinoff (p ());
    <==> { spinoff_equiv (p ()) }
    p ();
    ==> { () }
    tac_return_wp () p;
  }

let break_vc () : TAC unit break_wp =
  Classical.forall_intro aux;
  ()
#pop-options
