module SMTPatSymbols

val lem (x:int) : Lemma (x > x-1) [SMTPat (x-1 + 1)]
let lem (x:int) : Lemma (x > x-1) [SMTPat (x-1)] = ()
