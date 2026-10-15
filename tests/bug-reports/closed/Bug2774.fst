module Bug2774

type reflexive_relation (a:Type0) = rel:(a -> a -> prop){forall x. rel x x}

// The val groups the function arguments behind a refined type alias, while
// the let binds them explicitly. Both must have the same SMT interpretation.
val relation: #a:Type0 -> reflexive_relation (list a)
let relation #a l1 l2 =
  forall x. List.Tot.memP x l1 <==> List.Tot.memP x l2

val dumb_lemma:
  #a:Type0 -> l1:list a -> l2:list a ->
  Lemma
    (requires forall x. List.Tot.memP x l1 <==> List.Tot.memP x l2)
    (ensures l1 `relation` l2)
let dumb_lemma #a l1 l2 = ()
