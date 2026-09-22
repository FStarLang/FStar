open Prims
let rec gcd_nat (a : Prims.nat) (b : Prims.nat) : Prims.nat=
  if b = Prims.int_zero then a else gcd_nat b ((mod) a b)
let iabs (n : Prims.int) : Prims.nat= if n < Prims.int_zero then - n else n
let gcd (n : Prims.int) (d : Prims.pos) : Prims.pos= gcd_nat (iabs n) d
let reduced (n : Prims.int) (d : Prims.pos) : Prims.bool=
  (gcd n d) = Prims.int_one
