module FStar.UInt8
(* This module generated automatically using [mk_int.sh] *)

let n = 8

open FStar.UInt
open FStar.Mul

(* NOTE: anything that you fix/update here should be reflected in [FStar.IntN.fstp], which is mostly
 * a copy-paste of this module. *)

(* This is really the same thing as [FStar.IntN.fstp], with:
 * - every occurrence of [int_t] has been replaced with [uint_t]
 * - every occurrence of [@%] has been replaced with [%].
 *)

private type t' = | Mk: v:uint_t n -> t'
type t = t'

let v (x:t) : Tot (uint_t n) = x.v

val add: a:t -> b:t -> Pure t
  (requires (size (v a + v b) n))
  (ensures (fun c -> v a + v b = v c))
let add a b =
  Mk (add (v a) (v b))

val add_underspec: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c ->
    size (v a + v b) n ==> v a + v b = v c))
let add_underspec a b =
  Mk (add_underspec (v a) (v b))

val add_mod: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c -> (v a + v b) % pow2 n = v c))
let add_mod a b =
  Mk (add_mod (v a) (v b))

(* Subtraction primitives *)
val sub: a:t -> b:t -> Pure t
  (requires (size (v a - v b) n))
  (ensures (fun c -> v a - v b = v c))
let sub a b =
  Mk (sub (v a) (v b))

val sub_underspec: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c ->
    size (v a - v b) n ==> v a - v b = v c))
let sub_underspec a b =
  Mk (sub_underspec (v a) (v b))

val sub_mod: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c -> (v a - v b) % pow2 n = v c))
let sub_mod a b =
  Mk (sub_mod (v a) (v b))

(* Multiplication primitives *)
val mul: a:t -> b:t -> Pure t
  (requires (size (v a * v b) n))
  (ensures (fun c -> v a * v b = v c))
let mul a b =
  Mk (mul (v a) (v b))

val mul_underspec: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c ->
    size (v a * v b) n ==> v a * v b = v c))
let mul_underspec a b =
  Mk (mul_underspec (v a) (v b))

val mul_mod: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c -> (v a * v b) % pow2 n = v c))
let mul_mod a b =
  Mk (mul_mod (v a) (v b))

(* Division primitives *)
val div: a:t -> b:t{v b <> 0} -> Pure t
  (requires (size (v a / v b) n))
  (ensures (fun c -> v b <> 0 ==> v a / v b = v c))
let div a b =
  Mk (div (v a) (v b))

val div_underspec: a:t -> b:t{v b <> 0} -> Pure t
  (requires True)
  (ensures (fun c ->
    (v b <> 0 /\ size (v a / v b) n) ==> v a / v b = v c))
let div_underspec a b =
  Mk (div_underspec (v a) (v b))

(* Modulo primitives *)
val rem: a:t -> b:t{v b <> 0} -> Pure t
  (requires True)
  (ensures (fun c ->
    v a - ((v a / v b) * v b) = v c))
let rem a b = Mk (mod (v a) (v b))

(* Bitwise operators *)
val logand: t -> t -> Tot t
let logand a b = Mk (logand (v a) (v b))
val logxor: t -> t -> Tot t
let logxor a b = Mk (logxor (v a) (v b))
val logor: t -> t -> Tot t
let logor a b = Mk (logor (v a) (v b))
val lognot: t -> Tot t
let lognot a = Mk (lognot (v a))

val uint_to_t: x:(uint_t n) -> Pure t
  (requires True)
  (ensures (fun y -> v y = x))
let uint_to_t x = Mk x

(* Shift operators *)
val shift_right: a:t -> s:UInt32.t -> Pure t
  (requires True)
  (ensures (fun c -> UInt32.v s < n ==> v c = (v a / (pow2 (UInt32.v s)))))
let shift_right a s = Mk (shift_right (v a) (UInt32.v s))

val shift_left: a:t -> s:UInt32.t -> Pure t
  (requires True)
  (ensures (fun c -> UInt32.v s < n ==> v c = ((v a * pow2 (UInt32.v s)) % pow2 n)))
let shift_left a s = Mk (shift_left (v a) (UInt32.v s))

(* Comparison operators *)
let eq (a:t) (b:t) : Tot bool = eq #n (v a) (v b)
let gt (a:t) (b:t) : Tot bool = gt #n (v a) (v b)
let gte (a:t) (b:t) : Tot bool = gte #n (v a) (v b)
let lt (a:t) (b:t) : Tot bool = lt #n (v a) (v b)
let lte (a:t) (b:t) : Tot bool = lte #n (v a) (v b)

assume val eq_mask: a:t -> b:t -> Tot (c:t{(v a = v b ==> v c = pow2 n - 1) /\ (v a <> v b ==> v c = 0)})
assume val gte_mask: a:t -> b:t -> Tot (c:t{(v a >= v b ==> v c = pow2 n - 1) /\ (v a < v b ==> v c = 0)})

(* Infix notations *)
inline let op_Plus_Hat = add
inline let op_Plus_Question_Hat = add_underspec
inline let op_Plus_Percent_Hat = add_mod
inline let op_Subtraction_Hat = sub
inline let op_Subtraction_Question_Hat = sub_underspec
inline let op_Subtraction_Percent_Hat = sub_mod
inline let op_Star_Hat = mul
inline let op_Star_Question_Hat = mul_underspec
inline let op_Star_Percent_Hat = mul_mod
inline let op_Slash_Hat = div
inline let op_Percent_Hat = rem
inline let op_Hat_Hat = logxor
inline let op_Amp_Hat = logand
inline let op_Bar_Hat = logor
inline let op_Less_Less_Hat = shift_left
inline let op_Greater_Greater_Hat = shift_right
inline let op_Equals_Hat = eq
inline let op_Greater_Hat = gt
inline let op_Greater_Equals_Hat = gte
inline let op_Less_Hat = lt
inline let op_Less_Equals_Hat = lte

(* To input / output constants *)
assume val to_string: t -> Tot string
assume val of_string: string -> Tot t
type byte = t
