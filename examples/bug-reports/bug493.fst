module Bug493

val foo : x:('t -> nat -> Type) -> a:'t -> Lemma (x a 0 <==> x a 0)
let foo x a = ()
