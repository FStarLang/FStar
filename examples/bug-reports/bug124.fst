module Bug124Arithmetic

val test: a:int -> Lemma (requires (True))
                         (ensures (a - a + a = a)) 
let test a = ()

val test': a:int -> Lemma (requires (True))
                         (ensures ( a - a + a = (a - a) + a ))
let test' a = ()
