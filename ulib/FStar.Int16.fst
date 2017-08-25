module FStar.Int16
(* This module generated automatically using [mk_int.sh] *)

open FStar.Int
open FStar.Mul

(* NOTE: this file should remain synchronized with [FStar.UIntN.fstp] *)

private type t' = | Mk: v:int_t n -> t'
let t = t'

let v x = x.v

let v_inj x1 x2 = ()

let add a b = Mk (add (v a) (v b))

(* Subtraction primitives *)
let sub a b = Mk (sub (v a) (v b))

(* Multiplication primitives *)
let mul a b = Mk (mul (v a) (v b))

(* Division primitives *)
let div a b = Mk (div (v a) (v b))

(* Modulo primitives *)
let rem a b = Mk (mod (v a) (v b))

(* Bitwise operators *)
let logand a b = Mk (logand (v a) (v b))
let logxor a b = Mk (logxor (v a) (v b))
let logor a b = Mk (logor (v a) (v b))
let lognot a = Mk (lognot (v a))

let int_to_t x = Mk x

(* Shift operators *)
let shift_right a s = Mk (shift_right (v a) (UInt32.v s))

let shift_left a s = Mk (shift_left (v a) (UInt32.v s))

(* Comparison operators *)
let eq a b = eq #n (v a) (v b)
let gt a b = gt #n (v a) (v b)
let gte a b = gte #n (v a) (v b)
let lt a b = lt #n (v a) (v b)
let lte a b = lte #n (v a) (v b)

(* To input / output constants *)
let to_string = admit()
let of_string = admit()
