module NegativeTests.ZZImplicitFalse

val wtf: unit -> Lemma False
[@ fail] // error 19 (assertion failed) on 1-phase, error 66 (failed to resolve impl) on 2-phase
let wtf _ = let _:False = _ in ()
