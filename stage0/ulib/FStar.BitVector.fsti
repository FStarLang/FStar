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

module FStar.BitVector

/// This module defines a bit vector as a sequence of booleans of a
/// given length, and provides various utilities.
///
/// NOTE: THE TYPE [bv_t] DEFINED IS UNRELATED TO THE SMT SOLVER'S
/// THEORY OF BIT VECTORS. SEE [FStar.BV] FOR THAT.
///
/// TODO: We might rename this module to FStar.Seq.Boolean?

open FStar.Mul
open FStar.Seq.Base

(** [bv_t n] is just a sequence of booleans of length [n] *)
[@@do_not_unrefine]
type bv_t (n: nat) = vec: seq bool {length vec = n}

(**** Common constants *)

(** A length [n] zero vector *)
let zero_vec (#n: pos) : Tot (bv_t n) = create n false

(** A vector of length [n] whose [i]th bit is set, only *)
let elem_vec (#n: pos) (i: nat{i < n}) : Tot (bv_t n) = upd (create n false) i true

(** A length [n] vector all of whose bits are set *)
let ones_vec (#n: pos) : Tot (bv_t n) = create n true

(** Bitwise logical and *)
let rec logand_vec (#n: pos) (a b: bv_t n) : Tot (bv_t n) =
  if n = 1
  then create 1 (index a 0 && index b 0)
  else append (create 1 (index a 0 && index b 0)) (logand_vec #(n - 1) (slice a 1 n) (slice b 1 n))

(** [logand] defined in terms of its indexing behavior *)
val logand_vec_definition (#n: pos) (a b: bv_t n) (i: nat{i < n})
    : Lemma (ensures index (logand_vec #n a b) i = (index a i && index b i))
      [SMTPat (index (logand_vec #n a b) i)]

(** Bitwise logical exclusive or *)
let rec logxor_vec (#n: pos) (a b: bv_t n) : Tot (bv_t n) =
  if n = 1
  then create 1 (index a 0 <> index b 0)
  else append (create 1 (index a 0 <> index b 0)) (logxor_vec #(n - 1) (slice a 1 n) (slice b 1 n))

(** [logxor] defined in terms of its indexing behavior *)
val logxor_vec_definition (#n: pos) (a b: bv_t n) (i: nat{i < n})
    : Lemma (ensures index (logxor_vec #n a b) i = (index a i <> index b i))
      [SMTPat (index (logxor_vec #n a b) i)]

(** Bitwise logical or *)
let rec logor_vec (#n: pos) (a b: bv_t n) : Tot (bv_t n) =
  if n = 1
  then create 1 (index a 0 || index b 0)
  else append (create 1 (index a 0 || index b 0)) (logor_vec #(n - 1) (slice a 1 n) (slice b 1 n))

(** [logor] defined in terms of its indexing behavior *)
val logor_vec_definition (#n: pos) (a b: bv_t n) (i: nat{i < n})
    : Lemma (ensures index (logor_vec #n a b) i = (index a i || index b i))
      [SMTPat (index (logor_vec #n a b) i)]

(** Bitwise negation *)
let rec lognot_vec (#n: pos) (a: bv_t n) : Tot (bv_t n) =
  if n = 1
  then create 1 (not (index a 0))
  else append (create 1 (not (index a 0))) (lognot_vec #(n - 1) (slice a 1 n))

(** [lognot] defined in terms of its indexing behavior *)
val lognot_vec_definition (#n: pos) (a: bv_t n) (i: nat{i < n})
    : Lemma (ensures index (lognot_vec #n a) i = not (index a i))
      [SMTPat (index (lognot_vec #n a) i)]

(* Bitwise lemmas *)

(** If both [x] and [y] are false at a given index [i], then so is they logical xor at [i] *)
val lemma_xor_bounded (m: pos) (n: nat) (x y: bv_t m)
    : Lemma
      (requires
        (forall (i: nat).
            (i < m /\ i >= n) ==>
            (index x (m - 1 - i) = false /\ index y (m - 1 - i) = false)))
      (ensures
        (forall (i: nat). (i < m /\ i >= n) ==> (index (logxor_vec x y) (m - 1 - i) = false)))

(** The property that the zero bits of b are also zero in a.
    I.e. that a is a subset of b. *)
let is_subset_vec (#n: pos) (a b: bv_t n) =
  forall (i: nat). i < n ==> index b i = false ==> index a i = false

(** The property that the non-zero bits of b are also non-zero in a.
    I.e. that a is a superset of b. *)
let is_superset_vec (#n: pos) (a b: bv_t n) =
  forall (i: nat). i < n ==> index b i = true ==> index a i = true

(** Proves that the subset property is conserved in subslices. *)
val lemma_slice_subset_vec (#n: pos) (a b: bv_t n) (i: nat) (j: nat{i < j && j <= n})
    : Lemma (requires is_subset_vec a b)
      (ensures
        (match n with
          | 1 -> True
          | _ -> is_subset_vec #(j - i) (slice a i j) (slice b i j)))

(** Proves that the superset property is conserved in subslices. *)
val lemma_slice_superset_vec (#n: pos) (a b: bv_t n) (i: nat) (j: nat{i < j && j <= n})
    : Lemma (requires is_superset_vec a b)
      (ensures
        (match n with
          | 1 -> True
          | _ -> is_superset_vec #(j - i) (slice a i j) (slice b i j)))

(**** Shift operators *)

(* Note: the shift amount is extracted as a bitvector
   NS: Not sure what this remark means. *)

(** Shift [a] left by [s] bits, filling with zeroes *)
let shift_left_vec (#n: pos) (a: bv_t n) (s: nat) : Tot (bv_t n) =
  if s >= n then zero_vec #n else if s = 0 then a else append (slice a s n) (zero_vec #s)

(** The fill bits of a shift left are zero *)
val shift_left_vec_lemma_1 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i >= n - s})
    : Lemma (ensures index (shift_left_vec #n a s) i = false)
      [SMTPat (index (shift_left_vec #n a s) i)]

(** Relating the indexes of the shifted vector to the original *)
val shift_left_vec_lemma_2 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i < n - s})
    : Lemma (ensures index (shift_left_vec #n a s) i = index a (i + s))
      [SMTPat (index (shift_left_vec #n a s) i)]

(** Shift [a] right by [s] bits, filling with zeroes *)
let shift_right_vec (#n: pos) (a: bv_t n) (s: nat) : Tot (bv_t n) =
  if s >= n then zero_vec #n else if s = 0 then a else append (zero_vec #s) (slice a 0 (n - s))

(** The fill bits of a shift right are zero *)
val shift_right_vec_lemma_1 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i < s})
    : Lemma (ensures index (shift_right_vec #n a s) i = false)
      [SMTPat (index (shift_right_vec #n a s) i)]

(** Relating the indexes of the shifted vector to the original *)
val shift_right_vec_lemma_2 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i >= s})
    : Lemma (ensures index (shift_right_vec #n a s) i = index a (i - s))
      [SMTPat (index (shift_right_vec #n a s) i)]

(** Arithmetic shift right of [a], interpreting position [0] as the
    most-significant bit, and using its value to fill *)
let shift_arithmetic_right_vec (#n: pos) (a: bv_t n) (s: nat) : Tot (bv_t n) =
  if index a 0
  then if s >= n then ones_vec #n else if s = 0 then a else append (ones_vec #s) (slice a 0 (n - s))
  else shift_right_vec a s

(** The fill bits of arithmetic shift right is the value of its
    most-significant bit (position zero) *)
val shift_arithmetic_right_vec_lemma_1 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i < s})
    : Lemma (ensures index (shift_arithmetic_right_vec #n a s) i = index a 0)
      [SMTPat (index (shift_arithmetic_right_vec #n a s) i)]

(** Relating the indexes of the shifted vector to the original *)
val shift_arithmetic_right_vec_lemma_2 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i >= s})
    : Lemma (ensures index (shift_arithmetic_right_vec #n a s) i = index a (i - s))
      [SMTPat (index (shift_arithmetic_right_vec #n a s) i)]
