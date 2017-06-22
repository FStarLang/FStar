module Canon.Test
open FStar.Tactics
open Canon
open FStar.Mul
open FStar.Tactics.Canon // load it, to get the symbols for the lemmas

let test = 
  assert_by_tactic (compiled_canon())  (1 + 2 == 3 + 0)

let test2 (a b c d e : int) =
    assert_by_tactic (compiled_canon ())
        ((a+b+c+d+e)*(e+d+c+b+a) ==
                 a * a + a * b + a * c + a * d + a * e
                 + b * a + b * b + b * c + b * d + b * e
                 + c * a + c * b + c * c + c * d + c * e
                 + d * a + d * b + d * c + d * d + d * e
                 + e * a + e * b + e * c + e * d + e * e)
