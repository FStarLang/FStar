module PropImpredicativeAndNonStrictlyPositiveInductives

(* Only verifies with --__no_positivity *)
(* KM : And here goes my hope that prop is predicative enough to accept this kind of inductives... *)

open FStar.FunctionalExtensionality

let prop = p:Type0{forall (x y:p). x == y}
noeq type a = | IntroA : ((a -> prop) -> prop) -> a

let introA_injective (p p': (a -> prop) -> prop) : Lemma (IntroA p == IntroA p' ==> p == p) = ()

let inj (#x:Type) : x -> (x -> prop) = fun x0 y0 -> x0 == y0

let inj_injective (#x:Type) (x0 x0':x) : Lemma (requires (inj x0 `feq` inj x0')) (ensures (x0 == x0')) =
  assert (inj x0 x0) ;
  assert (inj x0 x0')

let f : (a -> prop) -> a = fun x -> IntroA (inj x)

let f_injective (p p' : a -> prop) : Lemma (requires (f p == f p')) (ensures (p == p')) =
  inj_injective p p' ;
  introA_injective (inj p) (inj p')

let p0 : a -> prop = fun x -> exists p. f p == x /\ ~(p x)
let x0 = f p0

open FStar.Classical

let bad1 () : Lemma (requires (p0 x0)) (ensures (~(p0 x0))) =
  let bidule (p:(a -> prop){f p == x0 /\ ~(p x0)}) : GTot (squash (~(p0 x0))) =
    f_injective p p0
  in
  exists_elim (~(p0 x0)) (FStar.Squash.get_proof (p0 x0)) bidule

let bad2 () : Lemma (requires (~(p0 x0))) (ensures (p0 x0)) =
  exists_intro (fun p -> f p == x0 /\ ~(p x0)) p0

let bad () : Lemma (p0 x0 <==> ~(p0 x0)) =
  move_requires bad1 () ;
  move_requires bad2 ()

let worse () : Lemma False = bad ()
