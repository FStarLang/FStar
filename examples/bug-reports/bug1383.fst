module Bug1383
let t (b: bool) : Tot Type0 = int -> Tot int
let t' (b: bool) (f: t b) : Tot Type0 = x:int -> Pure int (requires True) (ensures (fun y -> True))
let f : t true = fun x -> x
let test (x:nat) = assert (x == 0 \/ x =!= 0)
// val g : t' true f
// let g x = x

// // val f : t true
// // let f x = x
// // val g : t' true f
// // let g x = x
