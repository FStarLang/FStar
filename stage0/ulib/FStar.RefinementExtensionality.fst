module FStar.RefinementExtensionality

open FStar.FunctionalExtensionality
open FStar.PredicateExtensionality

let refext0 (t:Type) (r1 : t -> prop) (r2 : t -> prop) :
  Lemma (requires (r1 == r2))
        (ensures (x:t{r1 x} == x:t{r2 x})) = ()

let refext_on_domain (t:Type) (r1 : t -> prop) (r2 : t -> prop) :
  Lemma (requires (forall x. r1 x <==> r2 x))
        (ensures (x:t{on t r1 x} == x:t{on t r2 x})) =
  PredicateExtensionality.predicateExtensionality _ r1 r2;
  refext0 t (on t r1) (on t r2)

let refext (t:Type) (r1 : t -> prop) (r2 : t -> prop) :
  Lemma (requires (forall x. r1 x <==> r2 x))
        (ensures (x:t{r1 x} == x:t{r2 x})) =
  assert (x:t{on t r1 x} == x:t{r1 x});
  assert (x:t{on t r2 x} == x:t{r2 x});
  refext_on_domain t r1 r2;
  ()

(* Small test. Use names to avoid hash-consing mismatches. *)
let ref1 (x:int) : prop = b2t (x >= 0)
let ref2 (x:int) : prop = x >= 0 \/ x >= 1

let ty1 = x:int{ref1 x}
let ty2 = x:int{ref2 x}

let _ =
  refext int ref1 ref2;
  assert (ty1 == ty2)
