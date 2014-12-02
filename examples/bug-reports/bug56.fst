module Bug56

val g : x:'a -> Tot unit
let g x = ()

val xxx : x:int -> y:int -> Lemma (ensures (x > 0))
let rec xxx x y = g (xxx y)
