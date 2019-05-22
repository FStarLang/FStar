module FStar.ReflexiveTransitiveClosure

open FStar.Preorder

noeq
type closure (#a:Type0) (r:relation a) : a -> a -> Type0 =
| Refl: x:a -> closure r x x
| Step: x:a -> y:a -> r x y -> closure r x y
| Closure: x:a -> y:a -> z:a -> closure r x y -> closure r y z -> closure r x z

val closure_reflexive: #a:Type0 -> r:relation a -> Lemma (reflexive (closure r))

val closure_transitive: #a:Type0 -> r:relation a -> Lemma (transitive (closure r))

let reflexive_transitive_closure (#a:Type0) (r:relation a) : preorder a =
  closure_reflexive r;
  closure_transitive r;
  closure r

val stable_on_closure: #a:Type0 -> r:relation a -> p:(a -> Type0) 
  -> p_stable_on_r: (x:a -> y:a -> Lemma (requires p x /\ r x y) (ensures p y)) 
  -> Lemma (forall x y. p x /\ closure r x y ==> p y)
