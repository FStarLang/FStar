open Fstarcompiler
open Prims
let rec log_2 (x : Prims.pos) : Prims.nat=
  if x >= (Prims.of_int (2))
  then Prims.int_one + (log_2 (x / (Prims.of_int (2))))
  else Prims.int_zero
let rec powx (x : Prims.int) (n : Prims.nat) : Prims.int=
  match n with
  | uu___ when uu___ = Prims.int_zero -> Prims.int_one
  | n1 -> x * (powx x (n1 - Prims.int_one))
let abs (x : Prims.int) : Prims.int= if x >= Prims.int_zero then x else - x
let max (x : Prims.int) (y : Prims.int) : Prims.int= if x >= y then x else y
let min (x : Prims.int) (y : Prims.int) : Prims.int= if x >= y then y else x
let div (a : Prims.int) (b : Prims.pos) : Prims.int=
  if a < Prims.int_zero
  then
    (if ((mod) a b) = Prims.int_zero
     then - (- (a / b))
     else (- (- (a / b))) - Prims.int_one)
  else a / b
let div_non_eucl (a : Prims.int) (b : Prims.pos) : Prims.int=
  if a < Prims.int_zero
  then Prims.int_zero - ((Prims.int_zero - a) / b)
  else a / b
let shift_left (v : Prims.int) (i : Prims.nat) : Prims.int=
  v * (Prims.pow2 i)
let arithmetic_shift_right (v : Prims.int) (i : Prims.nat) : Prims.int=
  div v (Prims.pow2 i)
let signed_modulo (v : Prims.int) (p : Prims.pos) : Prims.int=
  if v >= Prims.int_zero
  then (mod) v p
  else Prims.int_zero - ((mod) (Prims.int_zero - v) p)
let op_Plus_Percent (a : Prims.int) (p : Prims.pos) : Prims.int=
  signed_modulo a p
