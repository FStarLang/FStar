module Bug209b

val foo : #t:Type{hasEq t} -> x:t -> Lemma (x = x)
let foo (#t:Type{hasEq t}) x = ()

val foo2 : t:Type{hasEq t} -> x:t -> Lemma (x = x)
let foo2 (t:Type{hasEq t}) x = ()
