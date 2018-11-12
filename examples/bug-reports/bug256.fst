module Bug256

assume type p : int -> Type

assume val witness: i:int{p i}


(* Fails to typecheck -- works now *)
val f1: unit -> i:int{p i}
let f1 = let g () = witness in g
(* This variant works: *)
(* let f1 = let g u = witness in g *)

(* Fails to typecheck -- works now *)
val f2: int -> ((i:int{p i}) * int)
let f2 = let g i = (witness,4) in g
