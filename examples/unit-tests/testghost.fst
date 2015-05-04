(*--build-config
    variables:LIB=../../lib;
    other-files:$LIB/ghost.fst
 --*)
module TestGhost
open Ghost

//let f (x:ghost int) = x + 1 //type-error; x is not an int

(*val g: ghost int -> Tot int
let g x = reveal x    //type-error: Ghost is not a sub-effect of pure
*)

//fine; having ghost effects in specifications is ok
val h: x:ghost int -> Pure (ghost int) (requires (reveal x >= 0)) (ensures (fun y -> x = y))
let h x = x

//fine; having ghost effects in specifications is ok
val i: x:ghost int -> Pure int (requires (reveal x = 0)) (ensures (fun y -> x = hide y))
let i x = 0 //fine

//fine; having ghost effects in specifications is ok
val j: x:ghost int -> Pure int (requires (reveal x = 0)) (ensures (fun y -> x = hide y))
let j x = 1 //logical failure
