
(* PropositionalExtensionality for the whole of Type0 is inconsistent,
   quite obviously since Type0 doesn't only include propositions *)

module PropositionalExtensionalityInconsistent
#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"

assume val propositionalExtensionality : unit ->
  Lemma (requires (True))
        (ensures (forall (p1:Type). forall (p2:Type). (p1 <==> p2) <==> p1==p2))

(* Inconsistent in F* -- proof by Kenji Maillard (adapted) *)

(* F* needs this extra int argument to "prove" int (inhabited) *)
let step (x:int) : Lemma (int <==> unit) = ()

let proof' () : Lemma (int <==> unit) = step 42

let clearly_wrong' () : Lemma (int == unit)
  = propositionalExtensionality(); proof'()

(* PredicateExtensionality provable from PropositionalExtensionality
   and FunctionalExtensionality, so also inconsistent *)

let predicate (a:Type0) = a -> Tot Type0

let peq (#a:Type0) (p1:predicate a) (p2:predicate a) = forall x. p1 x <==> p2 x

open FStar.FunctionalExtensionality

val predicateExtensionality : a:Type0 -> p1:predicate a -> p2:predicate a ->
  Lemma (requires True)
	(ensures (peq #a p1 p2 <==> p1==p2))
	(* [SMTPat (peq #a p1 p2)] *)
let predicateExtensionality (a:Type0) p1 p2 =
  propositionalExtensionality ();
  assert (feq #a #(fun _ -> Type0) p1 p2 <==> p1==p2)

(* Inconsistent in F* -- proof by Kenji Maillard *)

let p1 : predicate int = fun n -> int
let p2 : predicate int = fun n -> unit

let proof () : Lemma (p1 == p2) =
  predicateExtensionality int p1 p2

let zarb (p1 : predicate int) (p2:predicate int) : Lemma (requires (p1 == p2)) (ensures (p1 0 == p2 0)) = ()

let clearly_wrong () : Lemma (unit == int) = proof () ; zarb p1 p2

let test (n:int) : Lemma (has_type n unit) = clearly_wrong ()

let unit_contractible (a:Type) : Lemma (forall (x:a) (y:a). has_type x unit /\ has_type y unit ==> x == y) = ()

let ahahah () : Lemma (0 == 1) = test 0 ; test 1 ; unit_contractible int
