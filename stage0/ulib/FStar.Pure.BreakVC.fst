module FStar.Pure.BreakVC

open FStar.Tactics.V2

let mono_lem () : Lemma (pure_wp_monotonic unit break_wp') =
  assert (pure_wp_monotonic unit break_wp') by begin
    norm [delta];
    l_to_r [`spinoff_eq]
  end

let squash_p_impl_p (p:pure_post unit) : squash (squash (p ()) ==> p ()) = ()

#push-options "--no_tactics" // don't process `with_tactic` markers

let (==>>) = (==>) // Working around #3173 and #3175

let aux2 (p:pure_post unit)
: Lemma (break_wp p ==> pure_return unit () p)
= calc (==>>) {
    break_wp p;
    == {}
    spinoff (squash (p ()));
    ==> { spinoff_equiv (squash (p ())) }
    squash (p ());
    ==>> { squash_p_impl_p p }
    p ();
    ==> { () }
    pure_return unit () p;
  }

let break_vc () : PURE unit break_wp =
  Classical.forall_intro aux2;
  ()
#pop-options
