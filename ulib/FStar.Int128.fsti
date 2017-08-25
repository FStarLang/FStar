module FStar.Int128
(* This module generated automatically using [mk_int.sh] *)

let n = 128

open FStar.Int
open FStar.Mul

(* NOTE: this file should remain synchronized with [FStar.UIntN.fstip] *)

(* This is really the same thing as [FStar.UIntN.fstp], with:
  * - every occurrence of [uint_t] has been replaced with [int_t]
  * - every occurrence of [%] has been replaced with [@%].
  * - every occurrence of [/] has been replaced with [/%].
  * - the *_mod and *_underspec arithmetic functions have been removed since
      they have undefined behavior in C
  *)

val t: t:Type0{hasEq t}

val v : t -> Tot (int_t n)

val v_inj : x1:t -> x2:t ->
  Lemma (requires (v x1 == v x2))
        (ensures (x1 == x2))

val add: a:t -> b:t -> Pure t
  (requires (size (v a + v b) n))
  (ensures (fun c -> v a + v b = v c))

(* Subtraction primitives *)
val sub: a:t -> b:t -> Pure t
  (requires (size (v a - v b) n))
  (ensures (fun c -> v a - v b = v c))

(* Multiplication primitives *)
val mul: a:t -> b:t -> Pure t
  (requires (size (v a * v b) n))
  (ensures (fun c -> v a * v b = v c))

(* Division primitives *)
val div: a:t -> b:t{v b <> 0} -> Pure t
  (requires (size (v a / v b) n))
  (ensures (fun c -> v a / v b = v c))

(* Modulo primitives *)
val rem: a:t -> b:t{v b <> 0} -> Pure t
  (requires True)
  (ensures (fun c ->
    v a - ((v a / v b) * v b) = v c))

(* Bitwise operators *)
val logand: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun r -> v r = logand (v a) (v b)))
val logxor: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun r -> v r = logxor (v a) (v b)))
val logor: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun r -> v r = logor (v a) (v b)))
val lognot: a:t -> Pure t
  (requires True)
  (ensures (fun r -> v r = lognot (v a)))

val int_to_t: x:int_t n -> Pure t
  (requires True)
  (ensures (fun y -> v y = x))

//This private primitive is used internally by the
//compiler to translate bounded integer constants
//with a desugaring-time check of the size of the number,
//rather than an expensive verification check.
//Since it is marked private, client programs cannot call it directly
//Since it is marked unfold, it eagerly reduces,
//eliminating the verification overhead of the wrapper
private
unfold
let __int_to_t (x:int) : Tot t
    = admit(); int_to_t x

(* Shift operators *)
val shift_right: a:t -> s:UInt32.t -> Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> v c = (v a /% (pow2 (UInt32.v s)))))

val shift_left: a:t -> s:UInt32.t -> Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> v c = ((v a * pow2 (UInt32.v s)) @% pow2 n)))

(* Comparison operators *)
val eq : a:t -> b:t -> Pure bool
  (requires True)
  (ensures (fun r -> r == (v a = v b)))
val gt : a:t -> b:t -> Pure bool
  (requires True)
  (ensures (fun r -> r == (v a > v b)))
val gte : a:t -> b:t -> Pure bool
  (requires True)
  (ensures (fun r -> r == (v a >= v b)))
val lt : a:t -> b:t -> Pure bool
  (requires True)
  (ensures (fun r -> r == (v a < v b)))
val lte : a:t -> b:t -> Pure bool
  (requires True)
  (ensures (fun r -> r == (v a <= v b)))

(* Infix notations *)
unfold let op_Plus_Hat = add
unfold let op_Subtraction_Hat = sub
unfold let op_Star_Hat = mul
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
val to_string: t -> Tot string
val of_string: string -> Tot t

val mul_wide: a:Int64.t -> b:Int64.t -> Pure t
  (requires True)
  (ensures (fun c -> v c = Int64.v a * Int64.v b))
