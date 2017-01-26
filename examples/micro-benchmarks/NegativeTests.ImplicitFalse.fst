module NegativeTests.ImplicitFalse

val wtf: unit -> Lemma False
let wtf _ = let _:False = _ in ()
