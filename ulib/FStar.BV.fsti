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
val bv_uext (#n #m: pos) (a: bv_t n) : Tot (normalize (bv_t (m + n)))

(**** Relating unsigned integers to bitvectors *)

(** Mapping a bounded unsigned integer of size [< 2^n], to a n-length
    bit vector *)
val int2bv (#n: pos) (num: uint_t n) : Tot (bv_t n)

(** Mapping a bit vector back to a bounded unsigned integer of size [<
    2^n] *)
val bv2int (#n: pos) (vec: bv_t n) : Tot (uint_t n)

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

(**** Arithmetic operations *)
unfold
let bv_zero #n = int2bv #n 0

(** Inequality on bitvectors  *)
val bvult (#n: pos) (a b: bv_t n) : Tot (bool)

val int2bv_lemma_ult_1 (#n: pos) (a b: uint_t n)
    : Lemma (requires a < b) (ensures (bvult #n (int2bv #n a) (int2bv #n b)))

val int2bv_lemma_ult_2 (#n: pos) (a b: uint_t n)
    : Lemma (requires (bvult #n (int2bv #n a) (int2bv #n b))) (ensures a < b)

(** Addition *)
val bvadd (#n: pos) (a b: bv_t n) : Tot (bv_t n)

val int2bv_add:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvadd #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (add_mod #n x y) == z)

(** Subtraction *)
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


(** 'bvdiv_unsafe' is an uninterpreted function on 'bv_t n',
    modeling the corresponding operator from SMT-LIB.
    When its second argument is nonzero, the lemma below
    says that it is equivalent to bvdiv. *)
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

(** 'bvmod_unsafe' is an uninterpreted function on 'bv_t n',
    modeling the corresponding operator from SMT-LIB.
    When its second argument is nonzero, the lemma below
    says that it is equivalent to bvmod. *)
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

