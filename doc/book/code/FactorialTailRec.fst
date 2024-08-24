module FactorialTailRec
open FStar.Mul
open FStar.Ghost

//SNIPPET_START: factorial$
let rec factorial (n:nat)
  : GTot nat
  = if n = 0 then 1 else n * factorial (n - 1)
//SNIPPET_END: factorial$

//SNIPPET_START: factorial_tail$
let rec factorial_tail (n:nat) (out:nat)
  : Tot (r:nat { r == out * factorial n })
  = if n = 0 then out
    else factorial_tail (n - 1) (n * out)

let fact (n:nat) 
  : Tot (r:nat { r == factorial n })
  = factorial_tail n 1
//SNIPPET_END: factorial_tail$

//SNIPPET_START: factorial_bad$
[@@expect_failure]
let factorial_bad (n:nat) (out:nat)
  : Tot (r:nat { r == out * factorial n })
  = out * factorial n
//SNIPPET_END: factorial_bad$


//SNIPPET_START: factorial_tail_alt$
let rec factorial_tail_alt (n:nat) (out:nat)
  : Tot (r:nat { r == out * factorial n })
  = if n = 0 then out
    else (
      let f_n_1 = hide (factorial (n - 1)) in
      let result = factorial_tail_alt (n - 1) (n * out) in
      assert (result == (n * out) * f_n_1);
      result
    )
//SNIPPET_END: factorial_tail_alt$
