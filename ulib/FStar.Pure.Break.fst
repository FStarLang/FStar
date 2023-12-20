module FStar.Pure.Break

open FStar.Tactics.V2

#push-options "--no_tactics" // don't process `with_tactic` markers
let aux (p:Type0) : Lemma (requires (squash p)) (ensures (spinoff (squash p))) =
  spinoff_equiv (squash p)
#pop-options

let mono_lem () : Lemma (pure_wp_monotonic unit break_wp') =
  assert (pure_wp_monotonic unit break_wp') by begin
    norm [delta];
    l_to_r [`spinoff_eq]
  end

let ret_unit () : PURE unit (pure_return unit ()) = ()

let pure_str (wp1 wp2 : pure_wp unit)
         (f : unit -> PURE unit wp1)
         (_ : squash (forall p. wp2 p ==> wp1 p))
  : PURE unit wp2
  = f ()

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

let break () : PURE unit break_wp =
  Classical.forall_intro aux2;
  pure_str (pure_return unit ()) break_wp ret_unit ()
#pop-options
