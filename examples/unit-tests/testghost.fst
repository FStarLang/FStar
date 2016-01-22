(*--build-config
    other-files:FStar.Ghost.fst
 --*)
module TestGhost

open FStar.Ghost

//let f (x:erased int) = x + 1 //type-error; x is not an int

// val g: erased int -> Tot int
let g x = reveal x    //type-error: Erased is not a sub-effect of pure

//fine; having erased effects in specifications is ok
val h: x:erased int -> Pure (erased int) (requires (reveal x >= 0)) (ensures (fun y -> x = y))
let h x = x

//fine; having erased effects in specifications is ok
val i: x:erased int -> Pure int (requires (reveal x = 0)) (ensures (fun y -> x = hide y))
let i x = 0 //fine

//fine; having erased effects in specifications is ok
assume val j: x:erased int -> Pure int (requires (reveal x = 0))
                                       (ensures (fun y -> x = hide y))
//let j x = 1 -- logical failure
