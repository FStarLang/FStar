module FStar.UInt63
(* This module generated automatically using [mk_int.sh] *)

let n = 63

open FStar.UInt
open FStar.Mul

(* NOTE: this file should remain synchronized with [FStar.IntN.fstip] *)

val t: t:Type0{hasEq t}

val v : t -> Tot (uint_t n)

val v_inj : x1:t -> x2:t ->
  Lemma (requires (v x1 == v x2))
        (ensures (x1 == x2))

val add: a:t -> b:t -> Pure t
  (requires (size (v a + v b) n))
  (ensures (fun c -> v a + v b = v c))

val add_underspec: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c ->
    size (v a + v b) n ==> v a + v b = v c))

val add_mod: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c -> (v a + v b) % pow2 n = v c))

(* Subtraction primitives *)
val sub: a:t -> b:t -> Pure t
  (requires (size (v a - v b) n))
  (ensures (fun c -> v a - v b = v c))

val sub_underspec: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c ->
    size (v a - v b) n ==> v a - v b = v c))

val sub_mod: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c -> (v a - v b) % pow2 n = v c))

(* Multiplication primitives *)
val mul: a:t -> b:t -> Pure t
  (requires (size (v a * v b) n))
  (ensures (fun c -> v a * v b = v c))

val mul_underspec: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c ->
    size (v a * v b) n ==> v a * v b = v c))

val mul_mod: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c -> (v a * v b) % pow2 n = v c))

val mul_div: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c -> (v a * v b) / pow2 n = v c))

(* Division primitives *)
val div: a:t -> b:t{v b <> 0} -> Pure t
  (requires (True))
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

val uint_to_t: x:uint_t n -> Pure t
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
let __uint_to_t (x:int) : Tot t
    = admit(); uint_to_t x

(* Shift operators *)
val shift_right: a:t -> s:UInt32.t -> Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> v c = (v a / (pow2 (UInt32.v s)))))

val shift_left: a:t -> s:UInt32.t -> Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> v c = ((v a * pow2 (UInt32.v s)) % pow2 n)))

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

val eq_mask: a:t -> b:t -> Tot (c:t{(v a = v b ==> v c = pow2 n - 1) /\ (v a <> v b ==> v c = 0)})
val gte_mask: a:t -> b:t -> Tot (c:t{(v a >= v b ==> v c = pow2 n - 1) /\ (v a < v b ==> v c = 0)})

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
val to_string: t -> Tot string
val of_string: string -> Tot t
