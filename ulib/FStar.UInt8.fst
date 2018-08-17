module FStar.UInt8
(* This module generated automatically using [mk_int.sh] *)

unfold let n = 8

open FStar.UInt
open FStar.Mul

(* NOTE: anything that you fix/update here should be reflected in [FStar.IntN.fstp], which is mostly
 * a copy-paste of this module. *)

(* Except, as compared to [FStar.IntN.fstp], here:
 * - every occurrence of [int_t] has been replaced with [uint_t]
 * - every occurrence of [@%] has been replaced with [%].
 * - some functions (e.g., add_underspec, etc.) are only defined here, not on signed integers
 *)

abstract type t : eqtype =
  | Mk: v:uint_t n -> t

abstract
let v (x:t) : Tot (uint_t n) = x.v

abstract
let uint_to_t (x:uint_t n) : Pure t
  (requires True)
  (ensures (fun y -> v y = x)) = Mk x

let uv_inv (x : t) : Lemma
  (ensures (uint_to_t (v x) == x))
  [SMTPat (v x)] = ()

let vu_inv (x : uint_t n) : Lemma
  (ensures (v (uint_to_t x) == x))
  [SMTPat (uint_to_t x)] = ()

let v_inj (x1 x2: t): Lemma
  (requires (v x1 == v x2))
  (ensures (x1 == x2))
  = ()

abstract
let add (a:t) (b:t) : Pure t
  (requires (size (v a + v b) n))
  (ensures (fun c -> v a + v b = v c))
  = Mk (add (v a) (v b))

abstract
let add_underspec (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c ->
    size (v a + v b) n ==> v a + v b = v c))
 = Mk (add_underspec (v a) (v b))

abstract
let add_mod (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.add_mod (v a) (v b) = v c))
  = Mk (add_mod (v a) (v b))

(* Subtraction primitives *)
abstract
let sub (a:t) (b:t) : Pure t
  (requires (size (v a - v b) n))
  (ensures (fun c -> v a - v b = v c))
  = Mk (sub (v a) (v b))

abstract
let sub_underspec (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c ->
    size (v a - v b) n ==> v a - v b = v c))
  = Mk (sub_underspec (v a) (v b))

abstract
let sub_mod (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.sub_mod (v a) (v b) = v c))
  = Mk (sub_mod (v a) (v b))

(* Multiplication primitives *)
abstract
let mul (a:t) (b:t) : Pure t
  (requires (size (v a * v b) n))
  (ensures (fun c -> v a * v b = v c))
  = Mk (mul (v a) (v b))

abstract
let mul_underspec (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c ->
    size (v a * v b) n ==> v a * v b = v c))
   = Mk (mul_underspec (v a) (v b))

abstract
let mul_mod (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.mul_mod (v a) (v b) = v c))
  = Mk (mul_mod (v a) (v b))

abstract
let mul_div (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.mul_div (v a) (v b) = v c))
  = Mk (mul_div (v a) (v b))

(* Division primitives *)
abstract
let div (a:t) (b:t{v b <> 0}) : Pure t
  (requires (True))
  (ensures (fun c -> v a / v b = v c))
  = Mk (div (v a) (v b))

(* Modulo primitives *)
abstract
let rem (a:t) (b:t{v b <> 0}) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.mod (v a) (v b) = v c))
  = Mk (mod (v a) (v b))

(* Bitwise operators *)

abstract
let logand (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logand` v y = v z))
  = Mk (logand (v x) (v y))

abstract
let logxor (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logxor` v y == v z))
  = Mk (logxor (v x) (v y))

abstract
let logor (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logor` v y == v z))
  = Mk (logor (v x) (v y))

abstract
let lognot (x:t) : Pure t
  (requires True)
  (ensures (fun z -> lognot (v x) == v z))
  = Mk (lognot (v x))

(* Shift operators *)
abstract
let shift_right (a:t) (s:UInt32.t) : Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> FStar.UInt.shift_right (v a) (UInt32.v s) = v c))
  = Mk (shift_right (v a) (UInt32.v s))

abstract
let shift_left (a:t) (s:UInt32.t) : Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> FStar.UInt.shift_left (v a) (UInt32.v s) = v c))
  = Mk (shift_left (v a) (UInt32.v s))

(* Comparison operators *)
let eq (a:t) (b:t) : Tot bool = eq #n (v a) (v b)
let gt (a:t) (b:t) : Tot bool = gt #n (v a) (v b)
let gte (a:t) (b:t) : Tot bool = gte #n (v a) (v b)
let lt (a:t) (b:t) : Tot bool = lt #n (v a) (v b)
let lte (a:t) (b:t) : Tot bool = lte #n (v a) (v b)

abstract
let eq_mask (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> (v a = v b ==> v c = pow2 n - 1) /\
                  (v a <> v b ==> v c = 0)))
  = if v a = v b then Mk (pow2 n - 1)
    else Mk 0

abstract
let gte_mask (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> (v a >= v b ==> v c = pow2 n - 1) /\
                  (v a < v b ==> v c = 0)))
  = if v a >= v b then Mk (pow2 n - 1)
    else Mk 0

(* Infix notations *)
unfold let op_Plus_Hat = add
unfold let op_Plus_Question_Hat = add_underspec
unfold let op_Plus_Percent_Hat = add_mod
unfold let op_Subtraction_Hat = sub
unfold let op_Subtraction_Question_Hat = sub_underspec
unfold let op_Subtraction_Percent_Hat = sub_mod
unfold let op_Star_Hat = mul
unfold let op_Star_Question_Hat = mul_underspec
unfold let op_Star_Percent_Hat = mul_mod
unfold let op_Star_Slash_Hat = mul_div
unfold let op_Slash_Hat = div
unfold let op_Percent_Hat = rem
unfold let op_Hat_Hat = logxor
unfold let op_Amp_Hat = logand
unfold let op_Bar_Hat = logor
unfold let op_Less_Less_Hat = shift_left
unfold let op_Greater_Greater_Hat = shift_right
unfold let op_Equals_Hat = eq
unfold let op_Greater_Hat = gt
unfold let op_Greater_Equals_Hat = gte
unfold let op_Less_Hat = lt
unfold let op_Less_Equals_Hat = lte

(* To input / output constants *)
assume val to_string: t -> Tot string
assume val to_string_hex: t -> Tot string
assume val of_string: string -> Tot t

#set-options "--lax"
//This private primitive is used internally by the
//compiler to translate bounded integer constants
//with a desugaring-time check of the size of the number,
//rather than an expensive verifiation check.
//Since it is marked private, client programs cannot call it directly
//Since it is marked unfold, it eagerly reduces,
//eliminating the verification overhead of the wrapper
private
unfold
let __uint_to_t (x:int) : Tot t
    = uint_to_t x
#reset-options
unfold inline_for_extraction type byte = t
