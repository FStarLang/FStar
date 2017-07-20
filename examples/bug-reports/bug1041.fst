module Test

// Works
let f x : Lemma (True ==> x == x) = ()

// Fails
let f' x : Lemma (True -> x == x) = ()
