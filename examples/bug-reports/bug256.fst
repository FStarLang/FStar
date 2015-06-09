module Bug256


assume type P : int -> Type
assume val witness: i:int{P i}


(* Fails to typecheck *)
val f1: unit -> i:int{P i}
let f1 = let g () = witness in g
(* This variant works: *)
(* let f1 = let g u = witness in g *)

(* Fails to typecheck *)
val f2: int -> ((i:int{P i}) * int)
let f2 = let g i = (witness,4) in g
