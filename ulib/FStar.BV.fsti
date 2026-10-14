(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module FStar.BV

/// This module defines an abstract type of length-indexed bit
/// vectors.  The type and its operations are handled primitively in
/// F*'s SMT encoding, which maps them to the SMT sort of bit vectors
/// and operations on that sort. Note that this encoding only applies
/// when the length [n] is a syntactic literal: bit vectors with a
/// length referring to some variable, bound or otherwise, are encoded
/// as abstract sequences of bits.
///
/// Because of this syntactic encoding, it is also often helpful to
/// explicitly specify the bit length on all operations -- for example
/// constructing a 64-bit vector with [int2bv #64 1]. These explicit
/// annotations ensure that the encoding uses the literal length 64,
/// rather than inferring some variable as the length.
///
/// One way to use this module is in conjunction with
/// FStar.Tactics.BV. Its main tactic, [bv_tac], converts bitwise
/// operations on unsigned integers to operations on bit vectors and
/// back using the [int2bv / bv2int] isomorphism. This can be an
/// effective way of discharging such proof obligations for bitwise
/// operations on integers using the SMT solver's theory of
/// bitvectors.

open FStar.UInt
// for now just opening this for logand, logxor, etc. but we need a better solution.

(** The main type of this module, bit vectors of length [n], with
    decidable equality *)
val bv_t (n: nat) : eqtype

(* Experimental:
   Redefining basic type from UInt to avoid importing UInt
   Reduces verification time by 50% in small examples
// let max_int (n:nat) : Tot int = pow2 n - 1
// let min_int (n:nat) : Tot int = 0
// let fits (x:int) (n:nat) : Tot bool = min_int n <= x && x <= max_int n
// let size (x:int) (n:nat) : Tot Type0 = b2t(fits x n)
// type uint_t' (n:nat) = x:int{size x n}
*)

(** Extending a bit vector of length [n] to a larger vector of size
    [m+n], filling the extra bits with 0 *)
val bv_uext (#n #m: pos) (a: bv_t n) : Tot (bv_t (m + n))

(** Extract bits [i] through [j], inclusive, where bit 0 is the
    least-significant bit *)
val bv_extract
  (#n: pos)
  (a: bv_t n)
  (i: nat{i < n})
  (j: nat{j <= i})
  : Tot (bv_t (i - j + 1))

(** Concatenate two bit vectors, with [a] forming the high bits *)
val bv_concat (#n #m: pos) (a: bv_t n) (b: bv_t m) : Tot (bv_t (n + m))

(** Repeat a bit vector [i] times *)
val bv_repeat (#n #i: pos) (a: bv_t n) : Tot (bv_t (i * n))

(** Sign-extend a bit vector by [i] bits *)
val bv_sext (#n #i: pos) (a: bv_t n) : Tot (bv_t (i + n))

(**** Relating unsigned integers to bitvectors *)

(** Mapping a bounded unsigned integer of size [< 2^n], to a n-length
    bit vector *)
val int2bv (#n: pos) (num: uint_t n) : Tot (bv_t n)

(** Mapping a bit vector back to a bounded unsigned integer of size [<
    2^n] *)
val bv2int (#n: pos) (vec: bv_t n) : Tot (uint_t n)

(** Interpret a bit vector as a signed two's-complement integer *)
val sbv_to_int (#n: pos) (vec: bv_t n) : Tot (FStar.Int.int_t n)

(** Signed conversion is inverted by the corresponding unsigned bit pattern *)
val sbv_to_int_int2bv (#n: pos) (num: FStar.Int.int_t n)
  : Lemma
    (ensures
      (sbv_to_int #n (int2bv #n (FStar.Int.to_uint #n num)) == num))

val int2bv_lemma_1 (#n: pos) (a b: uint_t n)
    : Lemma (requires a = b) (ensures (int2bv #n a = int2bv #n b))

val int2bv_lemma_2 (#n: pos) (a b: uint_t n)
    : Lemma (requires (int2bv a = int2bv b)) (ensures a = b)

val inverse_vec_lemma (#n: pos) (vec: bv_t n)
    : Lemma (requires True) (ensures vec = (int2bv (bv2int vec))) [SMTPat (int2bv (bv2int vec))]

val inverse_num_lemma (#n: pos) (num: uint_t n)
    : Lemma (requires True)
      (ensures num = bv2int #n (int2bv #n num))
      [SMTPat (bv2int #n (int2bv #n num))]

val int2bv_bv_uext (#n #i: pos)
  (a: uint_t n)
  : Lemma
    (ensures (bv_uext #n #i (int2bv #n a) == int2bv #(i + n) (zero_extends #n i a)))

(** Extraction of an encoded integer selects the corresponding unsigned bits. *)
val int2bv_bv_extract (#n: pos)
  (a: uint_t n)
  (i: nat{i < n})
  (j: nat{j <= i})
  : Lemma
    (ensures
      (bv_extract #n (int2bv #n a) i j
       == int2bv #(i - j + 1)
            (FStar.UInt.to_uint_t (i - j + 1)
              ((a / pow2 j) % pow2 (i - j + 1)))))

(** Concatenation of encoded integers appends the low-order operand. *)
val int2bv_bv_concat (#n #m: pos) (a: uint_t n) (b: uint_t m)
  : Lemma
    (ensures
      (bv_concat #n #m (int2bv #n a) (int2bv #m b)
       == int2bv #(n + m) (FStar.UInt.to_uint_t (n + m) (a * pow2 m + b))))

(** Repetition agrees with the arithmetic geometric-sum model. *)
val int2bv_bv_repeat (#n #i: pos) (a: uint_t n)
  : Lemma
    (ensures
      (bv_repeat #n #i (int2bv #n a)
       == int2bv #(i * n)
            (FStar.UInt.to_uint_t (i * n)
              (a * ((pow2 (i * n) - 1) / (pow2 n - 1))))))

(** Sign extension preserves the represented signed integer. *)
val signed_int2bv_bv_sext (#n #i: pos) (a: FStar.Int.int_t n)
  : Lemma
    (ensures
      (bv_sext #n #i (int2bv #n (FStar.Int.to_uint #n a))
       == int2bv #(i + n)
            (FStar.Int.to_uint #(i + n) (FStar.Int.to_int_t (i + n) a))))

(**** Relating lists to bitvectors *)

(** Mapping a list of booleans to a bitvector *)
val list2bv (#n: pos) (l: list bool {List.length l = n}) : Tot (bv_t n)

(** Mapping a bitvector to a list of booleans *)
val bv2list: #n: pos -> bv_t n -> Tot (l: list bool {List.length l = n})

val list2bv_bij (#n: pos) (a: list bool {List.length a = n})
    : Lemma (requires (True)) (ensures (bv2list (list2bv #n a) = a))

val bv2list_bij (#n: pos) (a: bv_t n)
    : Lemma (requires (True)) (ensures (list2bv (bv2list #n a) = a))

(**** Bitwise logical operators *)

(** Bitwise conjunction *)
val bvand (#n: pos) (a b: bv_t n) : Tot (bv_t n)

val int2bv_logand:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvand #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (logand #n x y) == z)

(** Bitwise exclusive or *)
val bvxor (#n: pos) (a b: bv_t n) : Tot (bv_t n)

val int2bv_logxor:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvxor #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (logxor #n x y) == z)

(** Bitwise disjunction *)
val bvor (#n: pos) (a b: bv_t n) : Tot (bv_t n)

val int2bv_logor:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvor #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (logor #n x y) == z)

(** Bitwise negation *)
val bvnot (#n: pos) (a: bv_t n) : Tot (bv_t n)

val int2bv_lognot: #n: pos -> #x: uint_t n -> #z: bv_t n -> squash (bvnot #n (int2bv #n x) == z)
  -> Lemma (int2bv #n (lognot #n x) == z)

(** Two's-complement negation *)
val bvneg (#n: pos) (a: bv_t n) : Tot (bv_t n)

(** Two's-complement negation agrees with the signed integer model *)
val signed_int2bv_bvneg (#n: pos) (num: FStar.Int.int_t n)
  : Lemma
    (ensures
      (bvneg #n (int2bv #n (FStar.Int.to_uint #n num))
       == int2bv #n
            (FStar.Int.to_uint #n (FStar.Int.to_int_t n (-num)))))

(** Bitwise negated conjunction *)
val bvnand (#n: pos) (a b: bv_t n) : Tot (bv_t n)

(** Negated conjunction agrees with unsigned bitwise operations. *)
val int2bv_bvnand (#n: pos) (a b: uint_t n)
  : Lemma
    (ensures
      (bvnand #n (int2bv #n a) (int2bv #n b)
       == int2bv #n (lognot #n (logand #n a b))))

(** Bitwise negated disjunction *)
val bvnor (#n: pos) (a b: bv_t n) : Tot (bv_t n)

(** Negated disjunction agrees with unsigned bitwise operations. *)
val int2bv_bvnor (#n: pos) (a b: uint_t n)
  : Lemma
    (ensures
      (bvnor #n (int2bv #n a) (int2bv #n b)
       == int2bv #n (lognot #n (logor #n a b))))

(** Bitwise negated exclusive or *)
val bvxnor (#n: pos) (a b: bv_t n) : Tot (bv_t n)

(** Negated exclusive or agrees with unsigned bitwise operations. *)
val int2bv_bvxnor (#n: pos) (a b: uint_t n)
  : Lemma
    (ensures
      (bvxnor #n (int2bv #n a) (int2bv #n b)
       == int2bv #n (lognot #n (logxor #n a b))))

(** Return the one-bit vector [1] exactly when the operands are equal *)
val bvcomp (#n: pos) (a b: bv_t n) : Tot (bv_t 1)

(** Bit-vector comparison encodes unsigned equality as one bit. *)
val int2bv_bvcomp (#n: pos) (a b: uint_t n)
  : Lemma
    (ensures
      (bvcomp #n (int2bv #n a) (int2bv #n b)
       == int2bv #1 (if a = b then 1 else 0)))

(** Bitwise shift left: shift by bit-vector.
  This variant directly corresponds to the SMT-LIB bvshl function. In some
  cases, it may be more efficient to use this variant rather than the below
  natural number [bvshl] variant, as the below requires a conversion from
  unbounded integers. *)
val bvshl' (#n: pos) (a: bv_t n) (s: bv_t n) : Tot (bv_t n)

(** Bitwise shift left: shift by integer.
  This variant uses an unbounded natural and exists for compatibility. *)
val bvshl  (#n: pos) (a: bv_t n) (s: nat)    : Tot (bv_t n)

val int2bv_shl':
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvshl' #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (shift_left #n x y) == z)

val int2bv_shl:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvshl #n (int2bv #n x) y == z)
  -> Lemma (int2bv #n (shift_left #n x y) == z)

(** Bitwise shift right: shift by bit-vector.
  This variant directly corresponds to the SMT-LIB bvshr function. In some
  cases, it may be more efficient to use this variant rather than the below
  natural number [bvshr] variant, as the below requires a conversion from
  unbounded integers.
 *)
val bvshr' (#n: pos) (a: bv_t n) (s: bv_t n) : Tot (bv_t n)

(** Bitwise shift right: shift by integer.
  This variant uses an unbounded natural and exists for compatibility. *)
val bvshr  (#n: pos) (a: bv_t n) (s: nat)    : Tot (bv_t n)

val int2bv_shr':
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvshr' #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (shift_right #n x y) == z)

val int2bv_shr:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvshr #n (int2bv #n x) y == z)
  -> Lemma (int2bv #n (shift_right #n x y) == z)

(** Arithmetic shift right by a bit-vector amount *)
val bvashr (#n: pos) (a s: bv_t n) : Tot (bv_t n)

(** Arithmetic right shift corresponds to [FStar.Int.shift_arithmetic_right]. *)
val signed_int2bv_bvashr (#n: pos)
  (a: FStar.Int.int_t n)
  (s: uint_t n)
  : Lemma
    (ensures
      (bvashr #n (int2bv #n (FStar.Int.to_uint #n a)) (int2bv #n s)
       == int2bv #n
            (FStar.Int.to_uint #n (FStar.Int.shift_arithmetic_right #n a s))))

(**** Rotate operations *)

(** Bitwise rotate left: rotate by bit-vector. *)
val bvrol' (#n: pos) (a: bv_t n) (s: bv_t n) : Tot (bv_t n)

(** Bitwise rotate left: rotate by integer. *)
val bvrol  (#n: pos) (a: bv_t n) (s: nat)    : Tot (bv_t n)

val int2bv_rol':
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvrol' #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (rotate_left #n x y) == z)

val int2bv_rol:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvrol #n (int2bv #n x) y == z)
  -> Lemma (int2bv #n (rotate_left #n x y) == z)

(** Bitwise rotate right: rotate by bit-vector. *)
val bvror' (#n: pos) (a: bv_t n) (s: bv_t n) : Tot (bv_t n)

(** Bitwise rotate right: rotate by integer. *)
val bvror  (#n: pos) (a: bv_t n) (s: nat)    : Tot (bv_t n)

val int2bv_ror':
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvror' #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (rotate_right #n x y) == z)

val int2bv_ror:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvror #n (int2bv #n x) y == z)
  -> Lemma (int2bv #n (rotate_right #n x y) == z)

(**** Arithmetic operations *)
unfold
let bv_zero #n = int2bv #n 0

(** Inequality on bitvectors  *)
val bvult (#n: pos) (a b: bv_t n) : Tot (bool)

val int2bv_lemma_ult_1 (#n: pos) (a b: uint_t n)
    : Lemma (requires a < b) (ensures (bvult #n (int2bv #n a) (int2bv #n b)))

val int2bv_lemma_ult_2 (#n: pos) (a b: uint_t n)
    : Lemma (requires (bvult #n (int2bv #n a) (int2bv #n b))) (ensures a < b)

(** Unsigned comparisons *)
val bvule (#n: pos) (a b: bv_t n) : Tot bool
val bvugt (#n: pos) (a b: bv_t n) : Tot bool
val bvuge (#n: pos) (a b: bv_t n) : Tot bool

(** Unsigned less-than-or-equal agrees with integer comparison. *)
val int2bv_bvule (#n: pos) (a b: uint_t n)
  : Lemma
    (ensures (bvule #n (int2bv #n a) (int2bv #n b) == (a <= b)))

(** Unsigned greater-than agrees with integer comparison. *)
val int2bv_bvugt (#n: pos) (a b: uint_t n)
  : Lemma
    (ensures (bvugt #n (int2bv #n a) (int2bv #n b) == (a > b)))

(** Unsigned greater-than-or-equal agrees with integer comparison. *)
val int2bv_bvuge (#n: pos) (a b: uint_t n)
  : Lemma
    (ensures (bvuge #n (int2bv #n a) (int2bv #n b) == (a >= b)))

(** Signed two's-complement comparisons *)
val bvslt (#n: pos) (a b: bv_t n) : Tot bool
val bvsle (#n: pos) (a b: bv_t n) : Tot bool
val bvsgt (#n: pos) (a b: bv_t n) : Tot bool
val bvsge (#n: pos) (a b: bv_t n) : Tot bool

(** Signed comparisons agree with integer comparisons *)
val signed_int2bv_comparisons (#n: pos) (a b: FStar.Int.int_t n)
  : Lemma
    (ensures
      (bvslt #n (int2bv #n (FStar.Int.to_uint #n a))
                 (int2bv #n (FStar.Int.to_uint #n b)) == (a < b) /\
       bvsle #n (int2bv #n (FStar.Int.to_uint #n a))
                 (int2bv #n (FStar.Int.to_uint #n b)) == (a <= b) /\
       bvsgt #n (int2bv #n (FStar.Int.to_uint #n a))
                 (int2bv #n (FStar.Int.to_uint #n b)) == (a > b) /\
       bvsge #n (int2bv #n (FStar.Int.to_uint #n a))
                 (int2bv #n (FStar.Int.to_uint #n b)) == (a >= b)))

(** Addition *)
val bvadd (#n: pos) (a b: bv_t n) : Tot (bv_t n)

val int2bv_add:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvadd #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (add_mod #n x y) == z)

(** Minus *)
val bvsub (#n: pos) (a b: bv_t n) : Tot (bv_t n)

val int2bv_sub:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvsub #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (sub_mod #n x y) == z)

(** Division *)
val bvdiv (#n: pos) (a: bv_t n) (b: uint_t n {b <> 0}) : Tot (bv_t n)

val int2bv_div:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n {y <> 0} ->
    #z: bv_t n ->
    squash (bvdiv #n (int2bv #n x) y == z)
  -> Lemma (int2bv #n (udiv #n x y) == z)


(** SMT-LIB unsigned division, yielding all one bits when the divisor is zero. *)
val bvdiv_unsafe (#n: pos) (a b: bv_t n) : Tot (bv_t n)

(** 'bvdiv_unsafe' behaves as 'bvdiv' when denominator is nonzero *)
val bvdiv_unsafe_sound :
    #n: pos ->
    #a : bv_t n ->
    #b : bv_t n ->
    squash (bv2int b <> 0)
  -> Lemma (bvdiv_unsafe #n a b = bvdiv a (bv2int b))


(** Modulus *)
val bvmod (#n: pos) (a: bv_t n) (b: uint_t n {b <> 0}) : Tot (bv_t n)

val int2bv_mod:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n {y <> 0} ->
    #z: bv_t n ->
    squash (bvmod #n (int2bv #n x) y == z)
  -> Lemma (int2bv #n (mod #n x y) == z)

(** SMT-LIB unsigned remainder, yielding the dividend when the divisor is zero. *)
val bvmod_unsafe (#n: pos) (a b: bv_t n) : Tot (bv_t n)

(** 'bvmod_unsafe' behaves as 'bvmod' when denominator is nonzero *)
val bvmod_unsafe_sound :
    #n: pos ->
    #a : bv_t n ->
    #b : bv_t n ->
    squash (bv2int b <> 0)
  -> Lemma (bvmod_unsafe #n a b = bvmod a (bv2int b))

(** Multiplication modulo*)
val bvmul (#n: pos) (a: bv_t n) (b: uint_t n) : Tot (bv_t n)

val int2bv_mul:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvmul #n (int2bv #n x) y == z)
  -> Lemma (int2bv #n (mul_mod #n x y) == z)

(** Bit-vector multiplication *)
val bvmul' (#n: pos) (a b: bv_t n) : Tot (bv_t n)

val int2bv_mul':
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvmul' #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (mul_mod #n x y) == z)

(** Signed division, remainder, and modulo with SMT-LIB total semantics *)
val bvsdiv (#n: pos) (a b: bv_t n) : Tot (bv_t n)
val bvsrem (#n: pos) (a b: bv_t n) : Tot (bv_t n)
val bvsmod (#n: pos) (a b: bv_t n) : Tot (bv_t n)

(** Signed division agrees with truncating integer division *)
val signed_int2bv_bvsdiv (#n: pos)
  (a: FStar.Int.int_t n)
  (b: FStar.Int.int_t n{b <> 0})
  : Lemma
    (ensures
      (bvsdiv #n (int2bv #n (FStar.Int.to_uint #n a))
                  (int2bv #n (FStar.Int.to_uint #n b))
       == int2bv #n
            (FStar.Int.to_uint #n
              (FStar.Int.to_int_t n FStar.Int.(a /- b)))))

(** Signed remainder agrees with truncating integer division *)
val signed_int2bv_bvsrem (#n: pos)
  (a: FStar.Int.int_t n)
  (b: FStar.Int.int_t n{b <> 0})
  : Lemma
    (ensures
      (bvsrem #n (int2bv #n (FStar.Int.to_uint #n a))
                  (int2bv #n (FStar.Int.to_uint #n b))
       == int2bv #n
            (FStar.Int.to_uint #n (FStar.Int.mod #n a b))))

(** Signed modulo agrees with the SMT-LIB integer model *)
val signed_int2bv_bvsmod (#n: pos)
  (a: FStar.Int.int_t n)
  (b: FStar.Int.int_t n{b <> 0})
  : Lemma
    (ensures
    (let r = FStar.Int.mod #n a b in
       bvsmod #n (int2bv #n (FStar.Int.to_uint #n a))
                  (int2bv #n (FStar.Int.to_uint #n b))
       == int2bv #n
            (FStar.Int.to_uint #n
              (FStar.Int.to_int_t n
                (if r = 0 || (r < 0) = (b < 0) then r else r + b)))))

(** SMT-LIB overflow predicates *)
val bvnego (#n: pos) (a: bv_t n) : Tot bool
val bvuaddo (#n: pos) (a b: bv_t n) : Tot bool
val bvsaddo (#n: pos) (a b: bv_t n) : Tot bool
val bvumulo (#n: pos) (a b: bv_t n) : Tot bool
val bvsmulo (#n: pos) (a b: bv_t n) : Tot bool
val bvusubo (#n: pos) (a b: bv_t n) : Tot bool
val bvssubo (#n: pos) (a b: bv_t n) : Tot bool
val bvsdivo (#n: pos) (a b: bv_t n) : Tot bool

(** Signed negation overflow occurs exactly at the minimum integer. *)
val signed_int2bv_bvnego (#n: pos) (a: FStar.Int.int_t n)
  : Lemma
    (ensures
      (bvnego #n (int2bv #n (FStar.Int.to_uint #n a))
       == (a = FStar.Int.min_int n)))

(** Unsigned addition overflow agrees with the unbounded sum bound. *)
val int2bv_bvuaddo (#n: pos) (a b: uint_t n)
  : Lemma
    (ensures
      (bvuaddo #n (int2bv #n a) (int2bv #n b)
       == (a + b >= pow2 n)))

(** Signed addition overflow agrees with signed representability. *)
val signed_int2bv_bvsaddo (#n: pos)
  (a b: FStar.Int.int_t n)
  : Lemma
    (ensures
      (bvsaddo #n (int2bv #n (FStar.Int.to_uint #n a))
                   (int2bv #n (FStar.Int.to_uint #n b))
       == not (FStar.Int.fits (a + b) n)))

(** Unsigned multiplication overflow agrees with the unbounded product bound. *)
val int2bv_bvumulo (#n: pos) (a b: uint_t n)
  : Lemma
    (ensures
      (bvumulo #n (int2bv #n a) (int2bv #n b)
       == (a * b >= pow2 n)))

(** Signed multiplication overflow agrees with signed representability. *)
val signed_int2bv_bvsmulo (#n: pos)
  (a b: FStar.Int.int_t n)
  : Lemma
    (ensures
      (bvsmulo #n (int2bv #n (FStar.Int.to_uint #n a))
                   (int2bv #n (FStar.Int.to_uint #n b))
       == not (FStar.Int.fits (a * b) n)))

(** Unsigned subtraction overflow agrees with operand ordering. *)
val int2bv_bvusubo (#n: pos) (a b: uint_t n)
  : Lemma
    (ensures
      (bvusubo #n (int2bv #n a) (int2bv #n b) == (a < b)))

(** Signed subtraction overflow agrees with signed representability. *)
val signed_int2bv_bvssubo (#n: pos)
  (a b: FStar.Int.int_t n)
  : Lemma
    (ensures
      (bvssubo #n (int2bv #n (FStar.Int.to_uint #n a))
                   (int2bv #n (FStar.Int.to_uint #n b))
       == not (FStar.Int.fits (a - b) n)))

(** Signed division overflow is the minimum-integer divided by minus one case. *)
val signed_int2bv_bvsdivo (#n: pos)
  (a b: FStar.Int.int_t n)
  : Lemma
    (ensures
      (bvsdivo #n (int2bv #n (FStar.Int.to_uint #n a))
                   (int2bv #n (FStar.Int.to_uint #n b))
       == (a = FStar.Int.min_int n && b = -1)))
