module Bug1383
let t (b: bool) : Tot Type0 = int -> Tot int
let t' (b: bool) (f: t b) : Tot Type0 = x:int -> Pure int (requires True) (ensures (fun y -> True))
let f : t true = fun x -> x
val g : t' true f
let g x = x
