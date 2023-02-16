module FStar.Witnessed.Core
module P = FStar.Preorder

let s_predicate (state:Type u#a) = state -> Type0

let stable (state:Type u#a)
           (rel:P.preorder state)
           (p:s_predicate state) =
  forall s0 s1. (p s0 /\ rel s0 s1) ==> p s1

val witnessed (state:Type u#a)
              (rel:P.preorder state)
              (p:s_predicate state)
  : Type0

val witnessed_proof_irrelevant 
      (state:Type u#a)
      (rel:P.preorder state)
      (p:s_predicate state)
      (w0 w1:witnessed state rel p)
  : Lemma (w0 == w1)

