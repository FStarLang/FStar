
module Ex3c

val factorial: x:nat -> Tot nat
let rec factorial n = if n = 0 then 1 else n * factorial (n - 1)

val fact_lemma : x:nat{x >= 3} -> Lemma (factorial x >= 2*x)
