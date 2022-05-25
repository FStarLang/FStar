module Bug2552

assume val t: Type -> Type
assume val r (#a: Type) (w: t a) (x1: a) (x2: a) : Type0
assume val p (a: Type) : (w: t a{r w == precedes #a})

let lem () : Lemma (True) =
  assert (r (p nat) == precedes #nat)
