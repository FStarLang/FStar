module Bug1041

// Works
let f x : Lemma (True ==> x == x) = ()

// Fails
let f' x : Lemma (True -> x == x) = ()
