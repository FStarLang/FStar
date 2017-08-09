module FStar.UInt.Base

open FStar.Mul
open FStar.UInt.Types

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"
let mul_div #n a b =
  FStar.Math.Lemmas.lemma_mult_lt_sqr a b (pow2 n);
  (a * b) / (pow2 n)

#reset-options "--max_fuel 0 --max_ifuel 0"
let div #n a b =
  a / b

let div_size #n a b =
  FStar.Math.Lib.slash_decr_axiom a b; ()

let udiv #n a b =
  div_size #n a b;
  a / b

let mod_spec #n a b =
  FStar.Math.Lemmas.lemma_div_mod a b; ()

let incr_underspec #n a =
  if a < max_int n then a + 1 else magic()

let decr_underspec #n a =
  if a > min_int n then a - 1 else magic()

let add_underspec #n a b =
  if fits (a+b) n then a + b else magic ()

let sub_underspec #n a b =
  if fits (a-b) n then a - b else magic ()

let mul_underspec #n a b =
  if fits (a*b) n then a * b else magic ()

let div_underspec #n a b =
  if fits (a / b) n then a / b else magic ()
