module IntLib

open Axioms

(** Mathematical useful fonctions **)
(* Function : power of 2 *)
val pow2: n:nat -> GTot pos
let rec pow2 n =
  if n = 0 then 1
  else 2 * pow2 (n-1)

(* Function : power of x *)
val powx : x:int -> n:nat -> GTot int
let rec powx x n =
  match n with
  | 0 -> 1
  | _ -> x * powx x (n-1)

(* Function : absolute value *)
val abs: x:int -> GTot (y:int{ ((x >= 0) ==> ( y = x)) /\ ((x < 0) ==> y = -x) })
let abs x =
  if x >= 0 then x
  else -x

(* Function : maximum value *)
val max:
  x:int -> y:int -> GTot int
let max x y =
  if x >= y then x else y

(* Function : minimum value *)
val min: x:int -> y:int -> GTot int
let min x y =
  if x >= y then y else x

(* Function : standard euclidian division, the rest is always positive *)
val div_eucl: a:int -> b:pos -> GTot int
let div_eucl a b =
  if a < 0 then
    (if a % b = 0 then -(-a/b)
    else -(-a/b) -1)
  else a / b

(* General non-euclidian division operation *)
val div: a:int -> b:int{b <> 0} -> GTot int
let div a b = 
  if (a >= 0 && b < 0) || (a < 0 && b >= 0) then - (abs a / abs b)
  else abs a / abs b

(* General modulo *)
val mod: a:int -> b:int{b <> 0} -> GTot int
let mod a b = a % b //a - (div a b)

(* Circular modulo for modular arithmetic on signed words for isntance *)
val cmod: v:int -> p:pos{p%2=0} -> GTot int
let cmod v p =
  let m = v % p in
  if m >= p/2 then m - p else m
  
val log_2: x:pos -> GTot nat
let rec log_2 x = 
  if x >= 2 then 1 + log_2 (x / 2) else 0
