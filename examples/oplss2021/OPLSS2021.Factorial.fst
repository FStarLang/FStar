module OPLSS2021.Factorial
open FStar.Mul

let rec factorial (n:nat)
  : nat
  = if n = 0 then 1 else n * factorial (n - 1)

let rec factorial_increasing (n:nat)
  : _:unit{factorial n >= n}
  = if n <= 2 then ()
    else factorial_increasing (n - 1)

let rec factorial_increasing_lemma (n:nat)
  : Lemma (factorial n >= n)
  = if n <= 2 then ()
    else factorial_increasing_lemma (n - 1)
