module Bug256


assume type P : int -> Type
assume val witness: i:int{P i}


val f: unit -> i:int{P i}
let f = let g () = witness in g
