module SpecImplicits

(* A postcondition is a refinement of the result type, so it is part of the
   type an unannotated definition is inferred to have -- and unification can
   therefore recover a specification-valued implicit argument from it.  Before
   preconditions and postconditions moved into the type, none of the last three
   cases below could be accepted: the predicate had to come from unification
   against a *declared* type, or be written down. *)

assume val q : int -> prop
assume val lem (x:int) : Lemma (q x)
assume val app (#p:(int -> prop)) ($f: (x:int -> Lemma (p x))) : Lemma (forall x. p x)

(* [p] is determined by [lem]'s declared type. *)
let ok_named () : Lemma (forall x. q x) = app lem

(* [p] is written down. *)
let ok_explicit () : Lemma (forall x. q x) = app #(fun x -> q x) (fun x -> lem x)

(* [g]'s declared type determines [p]. *)
let ok_annotated () : Lemma (forall x. q x) =
  let g (x:int) : Lemma (q x) = lem x in
  app g

(* [p] is recovered from the type inferred for an unannotated local
   definition. *)
let ok_unannotated () : Lemma (forall x. q x) =
  let g = fun (x:int) -> lem x in
  app g

(* Likewise for a bare lambda. *)
let ok_lambda () : Lemma (forall x. q x) = app (fun x -> lem x)

(* And when the postcondition is trivial. *)
let ok_trivial () : Lemma (forall x. True) = app (fun x -> ())
