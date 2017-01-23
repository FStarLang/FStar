module Bug756



val e1 : f:(int -> Tot int) -> Lemma ((fun x -> f x) == f)
let e1 f = ()

val e2 : f:(int -> int -> Tot int) -> Lemma ((fun x -> f x) == f)
let e2 f = ()

val e3 : f:(int -> int -> Tot int) -> x:int -> Lemma ((fun y -> (f x) y) == (f x))
let e3 f x = admit () // e1 (f x)

open FStar.FunctionalExtensionality

val e3' : f:(int -> int -> Tot int) -> x:int -> Lemma ((fun y -> (f x) y) `feq` f x)
let e3' f x = () // e1 (f x)
