open Prims
let rec (log_2 : Prims.pos -> Prims.nat) =
  fun x ->
    if x >= (Prims.of_int (2))
    then Prims.int_one + (log_2 (x / (Prims.of_int (2))))
    else Prims.int_zero
let rec (powx : Prims.int -> Prims.nat -> Prims.int) =
  fun x ->
    fun n ->
      match n with
      | uu___ when uu___ = Prims.int_zero -> Prims.int_one
      | n1 -> x * (powx x (n1 - Prims.int_one))
let (abs : Prims.int -> Prims.int) =
  fun x -> if x >= Prims.int_zero then x else - x
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun x -> fun y -> if x >= y then x else y
let (min : Prims.int -> Prims.int -> Prims.int) =
  fun x -> fun y -> if x >= y then y else x
let (div : Prims.int -> Prims.pos -> Prims.int) =
  fun a ->
    fun b ->
      if a < Prims.int_zero
      then
        (if (a mod b) = Prims.int_zero
         then - (- (a / b))
         else (- (- (a / b))) - Prims.int_one)
      else a / b
let (div_non_eucl : Prims.int -> Prims.pos -> Prims.int) =
  fun a ->
    fun b ->
      if a < Prims.int_zero
      then Prims.int_zero - ((Prims.int_zero - a) / b)
      else a / b
let (shift_left : Prims.int -> Prims.nat -> Prims.int) =
  fun v -> fun i -> v * (Prims.pow2 i)
let (arithmetic_shift_right : Prims.int -> Prims.nat -> Prims.int) =
  fun v -> fun i -> div v (Prims.pow2 i)
let (signed_modulo : Prims.int -> Prims.pos -> Prims.int) =
  fun v ->
    fun p ->
      if v >= Prims.int_zero
      then v mod p
      else Prims.int_zero - ((Prims.int_zero - v) mod p)
let (op_Plus_Percent : Prims.int -> Prims.pos -> Prims.int) =
  fun a -> fun p -> signed_modulo a p