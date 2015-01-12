module Factorial

type nat = x:int{x >= 0}

// val factorial : int ->  ML int // F* infers this type by default
// val factorial : int ->  ML (x:int{x >= 1} // strong result type
// val factorial : int ->  x:int{x >= 1} // same as above
// val factorial : int -> Tot int // bad type, factorial not total by default
// val factorial : nat -> Tot int // need to restrict domain to prove totality
// val factorial : nat -> Tot nat // stronger result type
// val factorial : nat -> Tot (x:int{x >= 1}) // even stronger result type
let rec factorial n = if n = 0 then 1 else n * factorial (n - 1)
