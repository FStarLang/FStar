module SpecImplicits

(* A pre- or postcondition is a proof obligation, not part of the identity of a
   computation type, so it may not determine an implicit argument.  The
   predicate has to come from unification against a declared type, or be
   written down. *)

assume val q : int -> prop
assume val lem (x:int) : Lemma (q x)
assume val app (#p:(int -> prop)) ($f: (x:int -> Lemma (p x))) : Lemma (forall x. p x)

(* Accepted: [p] is determined by [lem]'s declared type. *)
let ok_named () : Lemma (forall x. q x) = app lem

(* Accepted: [p] is written down. *)
let ok_explicit () : Lemma (forall x. q x) = app #(fun x -> q x) (fun x -> lem x)

(* Accepted: [g]'s declared type determines [p]. *)
let ok_annotated () : Lemma (forall x. q x) =
  let g (x:int) : Lemma (q x) = lem x in
  app g

(* Rejected: [p] would have to be recovered from the verification condition of
   an unannotated local definition. *)
[@@expect_failure [66]]
let bad_unannotated () : Lemma (forall x. q x) =
  let g = fun (x:int) -> lem x in
  app g

(* Rejected: likewise for a bare lambda. *)
[@@expect_failure [66]]
let bad_lambda () : Lemma (forall x. q x) = app (fun x -> lem x)

(* Rejected even when the postcondition is genuinely trivial. *)
[@@expect_failure [66]]
let bad_trivial () : Lemma (forall x. True) = app (fun x -> ())
