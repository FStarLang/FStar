module Bug056

val g : x:'a -> Tot unit
let g x = ()

val xxx : x:int -> y:int -> Lemma (ensures (x = x))
let rec xxx x y = g (xxx y)
