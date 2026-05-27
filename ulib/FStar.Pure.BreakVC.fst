module FStar.Pure.BreakVC

open FStar.Tactics.V2

let mono_lem () : Lemma (pure_wp_monotonic unit break_wp') =
  assert (pure_wp_monotonic unit break_wp') by begin
    norm [delta];
    l_to_r [`spinoff_eq]
  end

#push-options "--no_tactics" // don't process `with_tactic` markers

let aux2 (p:pure_post unit)
: Lemma (break_wp p ==> pure_return unit () p)
= calc (==>) {
    break_wp p;
    == {}
    spinoff (p ());
    ==> { spinoff_equiv (p ()) }
    p ();
    ==> { () }
    pure_return unit () p;
  }

let break_vc () : PURE unit break_wp =
  Classical.forall_intro aux2;
  ()
#pop-options
