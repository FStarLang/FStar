module FStar.Tactics.BreakVC

open FStar.Tactics.V2

let mono_lem () : Lemma (tac_wp_monotonic #unit break_wp') =
  assert (tac_wp_monotonic #unit break_wp') by begin
    norm [delta];
    l_to_r [`spinoff_eq]
  end

let squash_p_impl_p (p:pure_post unit) : squash (squash (p ()) ==> p ()) = ()

#push-options "--no_tactics" // don't process `with_tactic` markers

let (==>>) = (==>) // Working around #3173 and #3175

let aux (p : unit -> Type0)
: Lemma (break_wp p ==> tac_return_wp () p)
= calc (==>>) {
    break_wp p;
    == {}
    spinoff (squash (p ()));
    <==> { spinoff_equiv (squash (p ())) }
    squash (p ());
    ==>> { squash_p_impl_p _ }
    p ();
    ==> { () }
    tac_return_wp () p;
  }

let break_vc () : TAC unit break_wp =
  Classical.forall_intro aux;
  ()
#pop-options
