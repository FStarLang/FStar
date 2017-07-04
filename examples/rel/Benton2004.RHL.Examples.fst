module Benton2004.RHL.Examples
open Benton2004.RHL

(* Section 4.2 *)

let sec42_ex1
  (x y z: var)
: Lemma
  (ensures (
    exec_equiv
      (gand (geq (gvar x Left) (gvar x Right)) (geq (gop op_Addition (gvar y Left) (gconst 1)) (gvar x Right)))
      (gand (geq (gvar x Left) (gvar x Right)) (geq (gvar z Left) (gvar z Right)))
      (assign z (eop op_Addition (evar y) (const 1)))
      (assign z (evar x))
  ))
= r_ass
    z
    z
    (eop op_Addition (evar y) (const 1))
    (evar x)
    (gand (geq (gvar x Left) (gvar x Right)) (geq (gvar z Left) (gvar z Right)))

let sec42_ex2
  (x y: var)
: Lemma
  (requires (x <> y)) // MISSING from the paper!
  (ensures (
    exec_equiv
      (gand (geq (gop op_Addition (gvar y Left) (gconst 1)) (gop op_Addition (gvar y Right) (gconst 1))) (geq (gop op_Addition (gvar y Left) (gconst 1)) (gop op_Addition (gvar y Right) (gconst 1))))
      (gand (geq (gvar x Left) (gvar x Right)) (geq (gop op_Addition (gvar y Left) (gconst 1)) (gvar x Right)))
      (assign x (eop op_Addition (evar y) (const 1)))
      (assign x (eop op_Addition (evar y) (const 1)))
  ))
= r_ass
    x
    x
    (eop op_Addition (evar y) (const 1))
    (eop op_Addition (evar y) (const 1))
    (gand (geq (gvar x Left) (gvar x Right)) (geq (gop op_Addition (gvar y Left) (gconst 1)) (gvar x Right)))

let sec42_ex3
  (y: var)
: Lemma
  (ensures (
    included
      (geq (gvar y Left) (gvar y Right))
      (gand (geq (gop op_Addition (gvar y Left) (gconst 1)) (gop op_Addition (gvar y Right) (gconst 1))) (geq (gop op_Addition (gvar y Left) (gconst 1)) (gop op_Addition (gvar y Right) (gconst 1))))
  ))
= ()

let sec42_ex4
  (x y: var)
: Lemma
  (requires (x <> y))
  (ensures (
    exec_equiv
      (geq (gvar y Left) (gvar y Right))
      (gand (geq (gvar x Left) (gvar x Right)) (geq (gop op_Addition (gvar y Left) (gconst 1)) (gvar x Right)))
      (assign x (eop op_Addition (evar y) (const 1)))
      (assign x (eop op_Addition (evar y) (const 1)))    
  ))
= sec42_ex2 x y;
  sec42_ex3 y
  // r_sub automatically applied

let sec42_ex5
  (x y z: var)
: Lemma
  (requires (x <> y))
  (ensures (
    exec_equiv
      (geq (gvar y Left) (gvar y Right))
      (gand (geq (gvar x Left) (gvar x Right)) (geq (gvar z Left) (gvar z Right)))
      (seq (assign x (eop op_Addition (evar y) (const 1))) (assign z (eop op_Addition (evar y) (const 1))))
      (seq (assign x (eop op_Addition (evar y) (const 1))) (assign z (evar x)))
  ))
= sec42_ex1 x y z;
  sec42_ex4 x y
  // r_seq automatically applied
