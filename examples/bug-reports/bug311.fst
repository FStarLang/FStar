module Bug311

// this works
val x : int
let x = 42

// this doesn't
val x' : y:int{y>0}
let x' = 42
// bug311.fst(12,0-12,11) : Error
// Effects PURE and ML cannot be composed
