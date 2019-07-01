module FStar.ReflexiveTransitiveClosure

open FStar.Preorder

val closure (#a:Type0) (r:relation a) : preorder a

val closure_step: #a:Type0 -> r:relation a -> x:a -> y:a
  -> Lemma (requires r x y) (ensures closure r x y)

val closure_inversion: #a:Type0 -> r:relation a -> x:a -> y:a
  -> Lemma (requires closure r x y)
          (ensures  x == y \/ r x y \/ (exists z. closure r x z /\ closure r z y))

val stable_on_closure: #a:Type0 -> r:relation a -> p:(a -> Type0)
  -> p_stable_on_r: (squash (forall x y. p x /\ r x y ==> p y))
  -> Lemma (forall x y. p x /\ closure r x y ==> p y)
