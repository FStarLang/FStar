module Bug2438

class test_typeclass a = {
  value: a;
}

assume new type test_type (t:Type0) {|test_typeclass t|}

assume val test_pred: #t:Type0 -> {|test_typeclass t|} -> test_type t -> bool

val test:
  #t:Type0 -> {| test_typeclass t |} -> #a:Type0 ->
  ps_b:(xa:a -> test_type t) -> Lemma ((forall (xaa:a). test_pred (ps_b xaa)))
