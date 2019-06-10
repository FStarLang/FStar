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

open FStar.Mul
open FStar.Seq

(* Define bitwise operators with new type BitVector. *)
type bv_t (n:nat) = vec:seq bool{length vec = n}

(* Constants *)
val zero_vec: #n:pos -> Tot (bv_t n)
let zero_vec #n = create n false
val elem_vec: #n:pos -> i:nat{i < n} -> Tot (bv_t n)
let elem_vec #n i = upd (create n false) i true
val ones_vec: #n:pos -> Tot (bv_t n)
let ones_vec #n = create n true

(* Bitwise operators *)
val logand_vec: #n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)
let rec logand_vec #n a b = 
  if n = 1 then create 1 (index a 0 && index b 0)
  else append (create 1 (index a 0 && index b 0)) (logand_vec #(n - 1) (slice a 1 n) (slice b 1 n))
  
val logxor_vec: #n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)
let rec logxor_vec #n a b = 
  if n = 1 then create 1 (index a 0 <> index b 0)
  else append (create 1 (index a 0 <> index b 0)) (logxor_vec #(n - 1) (slice a 1 n) (slice b 1 n))
  
val logor_vec: #n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)
let rec logor_vec #n a b = 
  if n = 1 then create 1 (index a 0 || index b 0)
  else append (create 1 (index a 0 || index b 0)) (logor_vec #(n - 1) (slice a 1 n) (slice b 1 n))
  
val lognot_vec: #n:pos -> a:bv_t n -> Tot (bv_t n)
let rec lognot_vec #n a = 
  if n = 1 then create 1 (not (index a 0))
  else append (create 1 (not (index a 0))) (lognot_vec #(n - 1) (slice a 1 n))

(* Bitwise operators definitions *)
val logand_vec_definition: #n:pos -> a:bv_t n -> b:bv_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (logand_vec #n a b) i = (index a i && index b i))
	[SMTPat (index (logand_vec #n a b) i)]
let rec logand_vec_definition #n a b i =
  if i = 0 then ()
  else logand_vec_definition #(n - 1) (slice a 1 n) (slice b 1 n) (i - 1)

val logxor_vec_definition: #n:pos -> a:bv_t n -> b:bv_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (logxor_vec #n a b) i = (index a i <> index b i))
	[SMTPat (index (logxor_vec #n a b) i)]
let rec logxor_vec_definition #n a b i =
  if i = 0 then ()
  else logxor_vec_definition #(n - 1) (slice a 1 n) (slice b 1 n) (i - 1)

val logor_vec_definition: #n:pos -> a:bv_t n -> b:bv_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (logor_vec #n a b) i = (index a i || index b i))
	[SMTPat (index (logor_vec #n a b) i)]
let rec logor_vec_definition #n a b i =
  if i = 0 then ()
  else logor_vec_definition #(n - 1) (slice a 1 n) (slice b 1 n) (i - 1)

val lognot_vec_definition: #n:pos -> a:bv_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (lognot_vec #n a) i = not (index a i))
	[SMTPat (index (lognot_vec #n a) i)]
let rec lognot_vec_definition #n a i =
  if i = 0 then ()
  else lognot_vec_definition #(n - 1) (slice a 1 n) (i - 1)

(* Bitwise lemmas *)

val lemma_xor_bounded: m:pos -> n:nat -> x:bv_t m -> y:bv_t m ->
  Lemma (requires (forall (i:nat). (i < m /\ i >= n) ==> (Seq.index x (m-1-i) = false /\ Seq.index y (m-1-i) = false)))
        (ensures  (forall (i:nat). (i < m /\ i >= n) ==> (Seq.index (logxor_vec x y) (m-1-i) = false)))
let lemma_xor_bounded m n x y = ()

(** is_subset_vec is the property that the zero bits of b are also zero in a.
    I.e. that a is a subset of b. *)
let is_subset_vec (#n:pos) (a:bv_t n) (b:bv_t n) =
  forall (i:nat). i < n ==> index b i = false ==> index a i = false

(** is_superset_vec is the property that the non-zero bits of b are also non-zero in a.
    I.e. that a is a superset of b. *)
let is_superset_vec (#n:pos) (a:bv_t n) (b:bv_t n) =
  forall (i:nat). i < n ==> index b i = true ==> index a i = true

(** lemma_slice_subset_vec proves that the subset property is conserved in subslices. *)
val lemma_slice_subset_vec: #n:pos -> a:bv_t n -> b:bv_t n -> i:nat -> j:nat{i < j && j <= n} ->
  Lemma (requires is_subset_vec a b)
  (ensures (match n with | 1 -> True | _ -> is_subset_vec #(j-i) (slice a i j) (slice b i j)))
let lemma_slice_subset_vec #n a b i j = ()

(** lemma_slice_superset_vec proves that the superset property is conserved in subslices. *)
val lemma_slice_superset_vec: #n:pos -> a:bv_t n -> b:bv_t n -> i:nat -> j:nat{i < j && j <= n} ->
  Lemma (requires is_superset_vec a b)
  (ensures (match n with | 1 -> True | _ -> is_superset_vec #(j-i) (slice a i j) (slice b i j)))
let lemma_slice_superset_vec #n a b i j = ()

(* Shift operators *)
(* Note: the shift amount is extracted as a bitvector*)
val shift_left_vec: #n:pos -> a:bv_t n -> s:nat -> Tot (bv_t n)
let shift_left_vec #n a s =
  if s >= n then zero_vec #n
  else if s = 0 then a
  else append (slice a s n) (zero_vec #s)
  
val shift_right_vec: #n:pos -> a:bv_t n -> s:nat -> Tot (bv_t n)
let shift_right_vec #n a s =
  if s >= n then zero_vec #n
  else if s = 0 then a
  else append (zero_vec #s) (slice a 0 (n - s))

val shift_arithmetic_right_vec: #n:pos -> a:bv_t n -> s:nat -> Tot (bv_t n)
let shift_arithmetic_right_vec #n a s =
  if index a 0 then
    if s >= n then ones_vec #n
    else if s = 0 then a
    else append (ones_vec #s) (slice a 0 (n - s))
  else shift_right_vec a s

(* Shift operators lemmas *)
val shift_left_vec_lemma_1: #n:pos -> a:bv_t n -> s:nat -> i:nat{i < n && i >= n - s} ->
  Lemma (requires True)
        (ensures index (shift_left_vec #n a s) i = false)
	[SMTPat (index (shift_left_vec #n a s) i)]
let shift_left_vec_lemma_1 #n a s i = ()

val shift_left_vec_lemma_2: #n:pos -> a:bv_t n -> s:nat -> i:nat{i < n && i < n - s} ->
  Lemma (requires True)
        (ensures index (shift_left_vec #n a s) i = index a (i + s))
	[SMTPat (index (shift_left_vec #n a s) i)]
let shift_left_vec_lemma_2 #n a s i = ()

val shift_right_vec_lemma_1: #n:pos -> a:bv_t n -> s:nat -> i:nat{i < n && i < s} ->
  Lemma (requires True)
        (ensures index (shift_right_vec #n a s) i = false)
	[SMTPat (index (shift_right_vec #n a s) i)]
let shift_right_vec_lemma_1 #n a s i = ()

val shift_right_vec_lemma_2: #n:pos -> a:bv_t n -> s:nat -> i:nat{i < n && i >= s} ->
  Lemma (requires True)
        (ensures index (shift_right_vec #n a s) i = index a (i - s))
	[SMTPat (index (shift_right_vec #n a s) i)]
let shift_right_vec_lemma_2 #n a s i = ()

val shift_arithmetic_right_vec_lemma_1: #n:pos -> a:bv_t n -> s:nat -> i:nat{i < n && i < s} ->
  Lemma (requires True)
        (ensures index (shift_arithmetic_right_vec #n a s) i = index a 0)
	[SMTPat (index (shift_arithmetic_right_vec #n a s) i)]
let shift_arithmetic_right_vec_lemma_1 #n a s i = ()

val shift_arithmetic_right_vec_lemma_2: #n:pos -> a:bv_t n -> s:nat -> i:nat{i < n && i >= s} ->
  Lemma (requires True)
        (ensures index (shift_arithmetic_right_vec #n a s) i = index a (i - s))
	[SMTPat (index (shift_arithmetic_right_vec #n a s) i)]
let shift_arithmetic_right_vec_lemma_2 #n a s i = ()
