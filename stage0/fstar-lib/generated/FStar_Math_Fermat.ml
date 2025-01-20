open Prims
let rec (pow : Prims.int -> Prims.nat -> Prims.int) =
  fun a ->
    fun k ->
      if k = Prims.int_zero
      then Prims.int_one
      else a * (pow a (k - Prims.int_one))
let rec (binomial : Prims.nat -> Prims.nat -> Prims.nat) =
  fun n ->
    fun k ->
      match (n, k) with
      | (uu___, uu___1) when uu___1 = Prims.int_zero -> Prims.int_one
      | (uu___, uu___1) when uu___ = Prims.int_zero -> Prims.int_zero
      | (uu___, uu___1) ->
          (binomial (n - Prims.int_one) k) +
            (binomial (n - Prims.int_one) (k - Prims.int_one))
let rec (factorial : Prims.nat -> Prims.pos) =
  fun uu___ ->
    match uu___ with
    | uu___1 when uu___1 = Prims.int_zero -> Prims.int_one
    | n -> n * (factorial (n - Prims.int_one))
let (op_Bang : Prims.nat -> Prims.pos) = fun n -> factorial n
let rec (sum :
  Prims.nat -> Prims.nat -> (Prims.nat -> Prims.int) -> Prims.int) =
  fun a ->
    fun b ->
      fun f -> if a = b then f a else (f a) + (sum (a + Prims.int_one) b f)