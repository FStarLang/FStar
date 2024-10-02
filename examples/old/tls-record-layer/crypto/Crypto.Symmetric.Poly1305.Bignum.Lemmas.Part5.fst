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
module Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part5

open FStar.Mul
open FStar.Ghost
(** Machine integers *)
open FStar.UInt64
(** Effects and memory layout *)
open FStar.HyperStack
(** Buffers *)
open FStar.Buffer
(** Mathematical definitions *)
open FStar.Math.Lib
open FStar.Math.Lemmas

open Crypto.Symmetric.Poly1305.Parameters
open Crypto.Symmetric.Poly1305.Bigint
open Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part1
open Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part2
open Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part3
open Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part4

module U64 = FStar.UInt64

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"


let carriedTopBottom (h0:mem) (h1:mem) (b:bigint) : GTot Type0 =
  live h0 b /\ live h1 b /\ length b >= norm_length+1
  /\ v (get h1 b 0) = v (get h0 b 0) + 5 * v (get h0 b 5)
  /\ v (get h1 b 1) = v (get h0 b 1)
  /\ v (get h1 b 2) = v (get h0 b 2)
  /\ v (get h1 b 3) = v (get h0 b 3)
  /\ v (get h1 b 4) = v (get h0 b 4)


val lemma_carry_top_10:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carried_1 h0 b /\ carriedTopBottom h0 h1 b))
	(ensures  (carried_1 h0 b /\ carriedTopBottom h0 h1 b /\ carried_2 h1 b))
let lemma_carry_top_10 h0 h1 b =
  assert_norm(pow2 3 = 8);
  pow2_plus 3 38;
  pow2_lt_compat 41 26;
  pow2_double_sum 41


val lemma_mod_6_p:
  b0:nat -> b1:nat -> b2:nat -> b3:nat -> b4:nat -> b5:nat -> p:pos ->
  Lemma	(ensures  (
    (b0 + pow2 26 * b1 + pow2 52 * b2 + pow2 78 * b3 + pow2 104 * b4 + pow2 130 * b5) % p
    = (b0 + pow2 26 * b1 + pow2 52 * b2 + pow2 78 * b3 + pow2 104 * b4 + (pow2 130) % p * b5) % p
  ))
let lemma_mod_6_p b0 b1 b2 b3 b4 b5 p =
  lemma_mod_plus_distr_l (pow2 130 * b5)
			 (b0 + pow2 26 * b1 + pow2 52 * b2 + pow2 78 * b3 + pow2 104 * b4)
			 p;
  lemma_mod_mul_distr_l (pow2 130) b5 p;
  lemma_mod_plus_distr_l ((pow2 130 % p) * b5)
			 (b0 + pow2 26 * b1 + pow2 52 * b2 + pow2 78 * b3 + pow2 104 * b4)
			 p


val lemma_carry_top_11:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carriedTopBottom h0 h1 b))
	(ensures  (carriedTopBottom h0 h1 b
	  /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime))
let lemma_carry_top_11 h0 h1 b =
  lemma_eval_bigint_6 h0 b;
  lemma_eval_bigint_5 h1 b;
  let b0 = v (get h0 b 0) in
  let b1 = v (get h0 b 1) in
  let b2 = v (get h0 b 2) in
  let b3 = v (get h0 b 3) in
  let b4 = v (get h0 b 4) in
  let b5 = v (get h0 b 5) in
  lemma_mod_6_p b0 b1 b2 b3 b4 b5 (reveal prime);
  lemma_2_130_modulo_prime ()


val lemma_carry_top_1:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carried_1 h0 b /\ carriedTopBottom h0 h1 b))
	(ensures  (carried_1 h0 b /\ carriedTopBottom h0 h1 b
	  /\ carried_2 h1 b
	  /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime))
let lemma_carry_top_1 h0 h1 b =
  lemma_carry_top_10 h0 h1 b;
  lemma_carry_top_11 h0 h1 b


let carried_4 (h:mem) (b:bigint) : GTot Type0 =
  live h b /\ v (get h b 0) < pow2 26 + 5
  /\ v (get h b 1) < pow2 26
  /\ (v (get h b 0) >= pow2 26 ==> v (get h b 1) < pow2 16)
  /\ v (get h b 2) < pow2 26
  /\ v (get h b 3) < pow2 26
  /\ v (get h b 4) < pow2 26


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_carry_top_20:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carried_3 h0 b /\ carriedTopBottom h0 h1 b))
	(ensures  (carried_3 h0 b /\ carried_4 h1 b))
let lemma_carry_top_20 h0 h1 b = ()


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_carry_top_2:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carried_3 h0 b /\ carriedTopBottom h0 h1 b))
	(ensures  (carried_3 h0 b /\ carriedTopBottom h0 h1 b
	  /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime
	  /\ carried_4 h1 b))
let lemma_carry_top_2 h0 h1 b =
  lemma_carry_top_20 h0 h1 b;
  lemma_carry_top_11 h0 h1 b


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

let isCarried01 (h0:mem) (h1:mem) (b:bigint) =
  live h0 b /\ live h1 b
  /\ v (get h1 b 0) = v (get h0 b 0) % pow2 26
  /\ v (get h1 b 1) = v (get h0 b 1) + (v (get h0 b 0) / pow2 26)
  /\ v (get h1 b 2) = v (get h0 b 2)
  /\ v (get h1 b 3) = v (get h0 b 3)
  /\ v (get h1 b 4) = v (get h0 b 4)

val lemma_div_lt2: a:nat -> b:pos{a < b} -> Lemma (a / b = 0)
let lemma_div_lt2 a b = ()


let lemma_norm_5 h (b:bigint) :
  Lemma (requires (live h b /\ v (get h b 0) < pow2 26 /\ v (get h b 1) < pow2 26
    /\ v (get h b 2) < pow2 26 /\ v (get h b 3) < pow2 26 /\ v (get h b 4) < pow2 26))
    (ensures (norm h b))
    = ()


#reset-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

val lemma_carry_0_to_10:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carried_4 h0 b /\ isCarried01 h0 h1 b))
	(ensures  (carried_4 h0 b /\ isCarried01 h0 h1 b /\ norm h1 b))
let lemma_carry_0_to_10 h0 h1 b =
  assert_norm (pow2 3 = 8);
  pow2_lt_compat 26 3;
  pow2_double_sum 26;
  lemma_div_lt (v (get h0 b 0)) 27 26;
  if (v (get h0 b 0) >= pow2 26) then (
    assert(v (get h0 b 1) < pow2 16);
    lemma_div_rest (v (get h0 b 0)) 3 26 )
  else lemma_div_lt2 (v (get h0 b 0)) (pow2 26);
  lemma_eval_bigint_5 h0 b;
  lemma_eval_bigint_5 h1 b;
  pow2_lt_compat 16 1;
  pow2_double_sum 16;
  pow2_lt_compat 26 17;
  lemma_mod_0 (v (get h0 b 0)) (pow2 26);
  cut(v (get h1 b 0) < pow2 26);
  cut(v (get h1 b 1) < pow2 26);
  cut(v (get h1 b 2) < pow2 26);
  cut(v (get h1 b 3) < pow2 26);
  cut(v (get h1 b 4) < pow2 26);
  lemma_norm_5 h1 b

val lemma_carry_0_to_11:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carried_4 h0 b /\ isCarried01 h0 h1 b))
	(ensures  (carried_4 h0 b /\ isCarried01 h0 h1 b /\ eval h1 b norm_length = eval h0 b norm_length))
let lemma_carry_0_to_11 h0 h1 b =
  lemma_eval_bigint_5 h0 b;
  lemma_eval_bigint_5 h1 b;
  cut (eval h1 b 5 =
    v (get h1 b 0) + pow2 26 * v (get h1 b 1) + pow2 52 * v (get h1 b 2)
		   + pow2 78 * v (get h1 b 3) + pow2 104 * v (get h1 b 4));
  cut (eval h1 b 5 =
    v (get h0 b 0) % pow2 26 + pow2 26 * (v (get h0 b 1) + v (get h0 b 0) / pow2 26)
      + pow2 52 * v (get h0 b 2) + pow2 78 * v (get h0 b 3) + pow2 104 * v (get h0 b 4));
  distributivity_add_right (pow2 26) (v (get h0 b 1)) (v (get h0 b 0) / pow2 26);
  cut (eval h1 b 5 =
    v (get h0 b 0) % pow2 26 + pow2 26 * (v (get h0 b 0) / pow2 26) + pow2 26 * (v (get h0 b 1))
      + pow2 52 * v (get h0 b 2) + pow2 78 * v (get h0 b 3) + pow2 104 * v (get h0 b 4));
  lemma_div_mod (v (get h0 b 0)) (pow2 26)


val lemma_carry_0_to_1:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carried_4 h0 b /\ isCarried01 h0 h1 b))
	(ensures  (carried_4 h0 b /\ isCarried01 h0 h1 b
	  /\ norm h1 b
	  /\ eval h1 b norm_length = eval h0 b norm_length))
let lemma_carry_0_to_1 h0 h1 b =
  lemma_carry_0_to_10 h0 h1 b;
  lemma_carry_0_to_11 h0 h1 b
