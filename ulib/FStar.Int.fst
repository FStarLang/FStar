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
module FStar.Int

(* NOTE: anything that you fix/update here should be reflected in [FStar.UInt.fst], which is mostly
 * a copy-paste of this module. *)

open FStar.Mul
open FStar.BitVector
open FStar.Math.Lemmas

let pow2_values x =
   match x with
   | 0  -> assert_norm (pow2 0 == 1)
   | 1  -> assert_norm (pow2 1 == 2)
   | 8  -> assert_norm (pow2 8 == 256)
   | 16 -> assert_norm (pow2 16 == 65536)
   | 31 -> assert_norm (pow2 31 == 2147483648)
   | 32 -> assert_norm (pow2 32 == 4294967296)
   | 63 -> assert_norm (pow2 63 == 9223372036854775808)
   | 64 -> assert_norm (pow2 64 == 18446744073709551616)
   | _  -> ()

let incr_underspec #n a =
  if a < max_int n then a + 1 else 0

let decr_underspec #n a =
  if a > min_int n then a - 1 else 0

let add_underspec #n a b =
  if fits (a+b) n then a + b else 0

let sub_underspec #n a b =
  if fits (a-b) n then a - b else 0

let mul_underspec #n a b =
  if fits (a*b) n then a * b else 0

let div_underspec #n a b =
  if fits (a / b) n then a / b else 0

let div_size #n a b =
  FStar.Math.Lib.slash_decr_axiom (abs a) (abs b)

let to_uint_injective #n x = ()

open FStar.Seq

let to_vec_lemma_1 #n a b = ()

let to_vec_lemma_2 #n a b = 
  UInt.to_vec_lemma_2 #n (to_uint a) (to_uint b)

#push-options "--initial_fuel 1 --max_fuel 1"
let rec inverse_aux #n vec i =
  if i = n - 1 then 
    assert((from_vec vec) % 2 = (if index vec (n - 1) then 1 else 0)) 
  else inverse_aux #(n - 1) (slice vec 0 (n - 1)) i
#pop-options

let inverse_vec_lemma #n vec = ()

let inverse_num_lemma #n num = ()

let from_vec_lemma_1 #n a b = ()

let from_vec_lemma_2 #n a b = inverse_vec_lemma a; inverse_vec_lemma b

let rec zero_to_vec_lemma #n i =
  if i = n - 1 then () else zero_to_vec_lemma #(n - 1) i

let zero_from_vec_lemma #n = to_vec_lemma_2 (from_vec (zero_vec #n)) (zero n)

let one_to_vec_lemma #n i =
  if i = n - 1 then () else zero_to_vec_lemma #n i

#push-options "--smtencoding.elim_box true --smtencoding.l_arith_repr native"
let rec pow2_to_vec_lemma #n p i =
  if i = n - 1 then ()
  else if p = 0 then one_to_vec_lemma #n i
  else pow2_to_vec_lemma #(n - 1) (p - 1) i
#pop-options

let pow2_from_vec_lemma #n p =
  to_vec_lemma_2 (from_vec (elem_vec #n p)) (pow2_n #n (n - p - 1))

let ones_to_vec_lemma #n i = ()

let ones_from_vec_lemma #n =
  to_vec_lemma_2 (from_vec (ones_vec #n)) (ones n)

let nth_lemma #n a b =
  assert(forall (i:nat{i < n}). index (to_vec #n a) i = index (to_vec #n b) i);
  to_vec_lemma_2 a b

let zero_nth_lemma #n i = ()

let one_nth_lemma #n i = ()

let ones_nth_lemma #n i = ()

let logand_definition #n a b i = ()

let logxor_definition #n a b i = ()

let logor_definition #n a b i = ()

let lognot_definition #n a i = ()

let logand_commutative #n a b = nth_lemma #n (logand #n a b) (logand #n b a)

let logand_associative #n a b c = 
  nth_lemma #n (logand #n (logand #n a b) c) (logand #n a (logand #n b c))

let logand_self #n a = nth_lemma #n (logand #n a a) a

let logand_lemma_1 #n a =
  nth_lemma #n (logand #n a (zero n)) (zero n)

let logand_lemma_2 #n a = 
  nth_lemma #n (logand #n a (ones n)) a

let sign_bit_negative #n a =
  UInt.from_vec_propriety #n (to_vec a) 1

let sign_bit_positive #n a =
  UInt.from_vec_propriety #n (to_vec a) 1

let logand_pos_le #n a b =
  UInt.logand_le (to_uint a) (to_uint b)

let logand_pow2_minus_one #n a m =
  UInt.logand_le (to_uint a) (to_uint (pow2_minus_one #n m))

#push-options "--z3rlimit_factor 2"
let logand_max #n a =
  sign_bit_positive a;
  sign_bit_positive #n (max_int n);
  nth_lemma a (logand a (max_int n))
#pop-options

let logxor_commutative #n a b = nth_lemma #n (logxor #n a b) (logxor #n b a)

let logxor_associative #n a b c = nth_lemma #n (logxor #n (logxor #n a b) c) (logxor #n a (logxor #n b c))

let logxor_self #n a = nth_lemma #n (logxor #n a a) (zero n)

let logxor_lemma_1 #n a = nth_lemma #n (logxor #n a (zero n)) a

let logxor_lemma_2 #n a = nth_lemma #n (logxor #n a (ones n)) (lognot #n a)

let logxor_inv #n a b =
  UInt.logxor_inv (to_uint a) (to_uint b)

let logxor_neq_nonzero #n a b = 
  UInt.logxor_neq_nonzero (to_uint a) (to_uint b)

let lognot_negative #n a =
  assert_norm (pow2 n = 2 * pow2 (n - 1));
  UInt.lemma_lognot_value_mod #n (a + pow2 n)

let shift_left_lemma_1 #n a s i = ()

let shift_left_lemma_2 #n a s i = ()

let shift_left_value_lemma #n a s =
  UInt.shift_left_value_lemma #n a s

let shift_right_lemma_1 #n a s i = ()

let shift_right_lemma_2 #n a s i = ()

let shift_arithmetic_right_lemma_1 #n a s i = ()

let shift_arithmetic_right_lemma_2 #n a s i = ()
