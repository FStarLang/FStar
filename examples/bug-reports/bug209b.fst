module Bug209_EDITED

val foo : #t:Type -> x:t -> Lemma (x = x)
let foo (#t:Type) x = ()

val foo2 : t:Type -> x:t -> Lemma (x = x)
let foo2 (t:Type) x = ()

val foo3 : x:'a -> Lemma (x = x)
let foo3 'a x = ()
