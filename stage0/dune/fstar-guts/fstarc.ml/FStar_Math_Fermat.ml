open Prims
let rec pow (a : Prims.int) (k : Prims.nat) : Prims.int=
  if k = Prims.int_zero
  then Prims.int_one
  else a * (pow a (k - Prims.int_one))
let rec binomial (n : Prims.nat) (k : Prims.nat) : Prims.nat=
  match (n, k) with
  | (uu___, uu___1) when uu___1 = Prims.int_zero -> Prims.int_one
  | (uu___, uu___1) when uu___ = Prims.int_zero -> Prims.int_zero
  | (uu___, uu___1) ->
      (binomial (n - Prims.int_one) k) +
        (binomial (n - Prims.int_one) (k - Prims.int_one))
let rec factorial (uu___ : Prims.nat) : Prims.pos=
  match uu___ with
  | uu___1 when uu___1 = Prims.int_zero -> Prims.int_one
  | n -> n * (factorial (n - Prims.int_one))
let op_Bang (n : Prims.nat) : Prims.pos= factorial n
let rec sum (a : Prims.nat) (b : Prims.nat) (f : Prims.nat -> Prims.int) :
  Prims.int= if a = b then f a else (f a) + (sum (a + Prims.int_one) b f)
