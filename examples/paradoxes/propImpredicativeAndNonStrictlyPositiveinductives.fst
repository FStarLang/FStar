module PropImpredicativeAndNonStrictlyPositiveInductives

(* Only verifies with --__no_positivity *)
(* KM : And here goes my hope that prop is predicative enough to accept this kind of inductives... *)

(* This code is a straightforward adaptation of the coq code at *)
(* http://vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive/ *)
(* which is itself a modernization of the counter-example found in *)
(* Thierry Coquand and Christine Paulin’s paper Inductively Defined Types (COLOG-88) *)

(* open FStar.FunctionalExtensionality *)

(* prop is not a universe per-se in F* but we can define the following type *)
(* (livinbg in Type1) which correspond to the homotopical h-prop. Due to squashing *)
(* in refinements it has some kind of impredicativity. Assuming functional *)
(* extensionality, it is also stable under product formation (at least when the *)
(* domain is in Type0 and the codomain in prop) *)
let prop = p:Type0{forall (x y:p). x == y}

(* The type a is positive but not strictly positive; *)
(* that's the first ingredient leading to an inconsistency *)
noeq type a = | IntroA : ((a -> prop) -> prop) -> a

let introA_injective (p p': (a -> prop) -> prop) : Lemma (IntroA p == IntroA p' ==> p == p) = ()

let inj (#x:Type) : x -> (x -> prop) = fun x0 y0 -> x0 == y0

let inj_injective (#x:Type) (x0 x0':x) : Lemma (requires (inj x0 == inj x0')) (ensures (x0 == x0')) =
  assert (inj x0 x0) ;
  assert (inj x0' x0)

let f : (a -> prop) -> a = fun x -> IntroA (inj x)

let f_injective (p p' : a -> prop) : Lemma (requires (f p == f p')) (ensures (p == p')) =
  inj_injective p p' ;
  introA_injective (inj p) (inj p')

(* As pointed out in the reference we use crucially the impredicativity of prop *)
(* when squashing down an existential on p of type (a -> prop) from Type1 to prop *)
let p0 : a -> prop = fun x ->
  exists (p:a -> prop).
    //NS: 04/30/18 ... added the annotation on p as part of revising type inference
    //Should be able to remove it as we move systematically to prop
    f p == x /\ ~(p x)
let x0 = f p0

open FStar.Classical

let bad1 () : Lemma (requires (p0 x0)) (ensures (~(p0 x0))) =
  let bidule (p:(a -> prop){f p == x0 /\ ~(p x0)}) : GTot (squash (~(p0 x0))) =
    f_injective p p0
  in
  exists_elim (~(p0 x0)) (FStar.Squash.get_proof (p0 x0)) bidule

let bad2 () : Lemma (requires (~(p0 x0))) (ensures (p0 x0)) =
  exists_intro (fun (p:a -> prop) ->
    //NS: 04/30/18 ... added the annotation on p as part of revising type inference
    //Should be able to remove it as we move systematically to prop
    f p == x0 /\ ~(p x0)) p0

let bad () : Lemma (p0 x0 <==> ~(p0 x0)) =
  move_requires bad1 () ;
  move_requires bad2 ()

let worse () : Lemma False = bad ()
