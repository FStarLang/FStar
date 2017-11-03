module Opaque_i

val make_opaque : #a:Type -> a -> a
val reveal_opaque : #a:Type -> x:a -> Lemma (x == make_opaque x)
