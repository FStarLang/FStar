module FStar.PropositionalExtensionality
assume val axiom : unit -> Lemma (forall (p1:prop) (p2:prop). (p1 <==> p2) <==> (p1 == p2))
