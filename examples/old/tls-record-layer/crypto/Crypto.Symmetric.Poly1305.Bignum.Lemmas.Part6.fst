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
module Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part6

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

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack

open FStar.Buffer.Quantifiers
open Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part1
open Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part2
open Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part3
open Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part4
open Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part5

let prime = prime
let satisfiesModuloConstraints h b = satisfiesModuloConstraints h b
let isSum h h1 a b = isSum h h1 a b
let bound27 h b = bound27 h b
let w : U32.t -> Tot int = U32.v


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

let u26 = x:U64.t{v x < pow2 26}


let maskPrime mask b0 b1 b2 b3 b4 : Type0 =
  (v mask = pow2 64 - 1 ==> (v b4 = pow2 26 - 1 /\ v b3 = pow2 26 - 1 /\ v b2 = pow2 26 - 1 /\ v b1 = pow2 26 - 1 /\ v b0 >= pow2 26 - 5))
  /\ (v mask = 0 ==> (v b4 < pow2 26 - 1 \/ v b3 < pow2 26 -1 \/ v b2 < pow2 26 - 1 \/ v b1 < pow2 26 - 1 \/ v b0 < pow2 26 - 5))


let masked mask b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' : Type0 =
  (v mask = pow2 64 - 1 ==> (v b4' = v b4 - (pow2 26 - 1) /\ v b3' = v b3 - (pow2 26 - 1) /\ v b2' = v b2 - (pow2 26 - 1) /\ v b1' = v b1 - (pow2 26 - 1) /\ v b0' = v b0 - (pow2 26 - 5)))
  /\ (v mask = 0 ==> (v b4' = v b4 /\ v b3' = v b3 /\ v b2' = v b2 /\ v b1' = v b1 /\ v b0' = v b0))

let lemma_mult_le_left (a:pos) (b:nat) (c:nat) : Lemma (requires (b <= c)) (ensures (a * b <= a * c))
  = ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val lemma_finalize_1:
  b0:u26 -> b1:u26 -> b2:u26 -> b3:u26 -> b4:u26 ->
  b0':u26 -> b1':u26 -> b2':u26 -> b3':u26 -> b4':u26 ->
  mask:U64.t{v mask = 0 \/ v mask = pow2 64 - 1} ->
  Lemma
    (requires (maskPrime mask b0 b1 b2 b3 b4 /\ masked mask b0 b1 b2 b3 b4 b0' b1' b2' b3' b4'))
    (ensures  (v b0' + pow2 26 * v b1' + pow2 52 * v b2' + pow2 78 * v b3' + pow2 104 * v b4' < pow2 130 - 5) )
let lemma_finalize_1 b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' mask =
  let res = v b0' + pow2 26 * v b1' + pow2 52 * v b2' + pow2 78 * v b3' + pow2 104 * v b4' in
  if v mask = pow2 64 - 1 then (
    cut (res < 5); assert_norm (5 < pow2 130 - 5)
  ) else (
    if (v b0 < pow2 26 - 5) then (
      lemma_mult_le_left (pow2 26) (v b1') (pow2 26 - 1);
      lemma_mult_le_left (pow2 52) (v b2') (pow2 26 - 1);
      lemma_mult_le_left (pow2 78) (v b3') (pow2 26 - 1);
      lemma_mult_le_left (pow2 104) (v b4') (pow2 26 - 1);
      cut (res <= (pow2 26 - 6) + pow2 26 * (pow2 26 - 1) + pow2 52 * (pow2 26 - 1)
          + pow2 78 * (pow2 26 - 1) + pow2 104 * (pow2 26 - 1));
      assert_norm((pow2 26 - 6) + pow2 26 * (pow2 26 - 1) + pow2 52 * (pow2 26 - 1)
          + pow2 78 * (pow2 26 - 1) + pow2 104 * (pow2 26 - 1) < pow2 130 - 5)
    ) else if (v b1 < pow2 26 - 1) then (
      lemma_mult_le_left (pow2 26) (v b1') (pow2 26 - 2);
      lemma_mult_le_left (pow2 52) (v b2') (pow2 26 - 1);
      lemma_mult_le_left (pow2 78) (v b3') (pow2 26 - 1);
      lemma_mult_le_left (pow2 104) (v b4') (pow2 26 - 1);
      cut (res <= (pow2 26 - 1) + pow2 26 * (pow2 26 - 2) + pow2 52 * (pow2 26 - 1)
          + pow2 78 * (pow2 26 - 1) + pow2 104 * (pow2 26 - 1));
      assert_norm((pow2 26 - 1) + pow2 26 * (pow2 26 - 2) + pow2 52 * (pow2 26 - 1)
          + pow2 78 * (pow2 26 - 1) + pow2 104 * (pow2 26 - 1) < pow2 130 - 5)
    ) else if (v b2 < pow2 26 - 1) then (
      lemma_mult_le_left (pow2 26) (v b1') (pow2 26 - 1);
      lemma_mult_le_left (pow2 52) (v b2') (pow2 26 - 2);
      lemma_mult_le_left (pow2 78) (v b3') (pow2 26 - 1);
      lemma_mult_le_left (pow2 104) (v b4') (pow2 26 - 1);
      cut (res <= (pow2 26 - 1) + pow2 26 * (pow2 26 - 1) + pow2 52 * (pow2 26 - 2)
          + pow2 78 * (pow2 26 - 1) + pow2 104 * (pow2 26 - 1));
      assert_norm((pow2 26 - 1) + pow2 26 * (pow2 26 - 1) + pow2 52 * (pow2 26 - 2)
          + pow2 78 * (pow2 26 - 1) + pow2 104 * (pow2 26 - 1) < pow2 130 - 5)
    ) else if (v b3 < pow2 26 - 1) then (
      lemma_mult_le_left (pow2 26) (v b1') (pow2 26 - 1);
      lemma_mult_le_left (pow2 52) (v b2') (pow2 26 - 1);
      lemma_mult_le_left (pow2 78) (v b3') (pow2 26 - 2);
      lemma_mult_le_left (pow2 104) (v b4') (pow2 26 - 1);
      cut (res <= (pow2 26 - 1) + pow2 26 * (pow2 26 - 1) + pow2 52 * (pow2 26 - 1)
          + pow2 78 * (pow2 26 - 2) + pow2 104 * (pow2 26 - 1));
      assert_norm((pow2 26 - 1) + pow2 26 * (pow2 26 - 1) + pow2 52 * (pow2 26 - 1)
          + pow2 78 * (pow2 26 - 2) + pow2 104 * (pow2 26 - 1) < pow2 130 - 5)
    ) else  (
      lemma_mult_le_left (pow2 26) (v b1') (pow2 26 - 1);
      lemma_mult_le_left (pow2 52) (v b2') (pow2 26 - 1);
      lemma_mult_le_left (pow2 78) (v b3') (pow2 26 - 1);
      lemma_mult_le_left (pow2 104) (v b4') (pow2 26 - 2);
      cut (res <= (pow2 26 - 1) + pow2 26 * (pow2 26 - 1) + pow2 52 * (pow2 26 - 1)
          + pow2 78 * (pow2 26 - 1) + pow2 104 * (pow2 26 - 2));
      assert_norm((pow2 26 - 1) + pow2 26 * (pow2 26 - 1) + pow2 52 * (pow2 26 - 1)
          + pow2 78 * (pow2 26 - 1) + pow2 104 * (pow2 26 - 2) < pow2 130 - 5)
    )
  )



#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val lemma_finalize_2:
  b0:u26 -> b1:u26 -> b2:u26 -> b3:u26 -> b4:u26 ->
  b0':u26 -> b1':u26 -> b2':u26 -> b3':u26 -> b4':u26 ->
  mask:U64.t{v mask = 0 \/ v mask = pow2 64 - 1} ->
  Lemma
    (requires (maskPrime mask b0 b1 b2 b3 b4 /\ masked mask b0 b1 b2 b3 b4 b0' b1' b2' b3' b4'))
    (ensures  ((v b0 + pow2 26 * v b1 + pow2 52 * v b2 + pow2 78 * v b3 + pow2 104 * v b4) % (pow2 130 - 5) = (v b0' + pow2 26 * v b1' + pow2 52 * v b2' + pow2 78 * v b3' + pow2 104 * v b4') % (pow2 130 - 5)))
let lemma_finalize_2 b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' mask =
  let res = v b0' + pow2 26 * v b1' + pow2 52 * v b2' + pow2 78 * v b3' + pow2 104 * v b4' in
  let res0 = v b0 + pow2 26 * v b1 + pow2 52 * v b2 + pow2 78 * v b3 + pow2 104 * v b4 in
  if v mask = 0 then (
    ()
  ) else (
    cut (res = v b0 - (pow2 26 - 5) + pow2 26 * (v b1 - (pow2 26 - 1))
               + pow2 52 * (v b2 - (pow2 26 - 1)) + pow2 78 * (v b3 - (pow2 26 - 1))
               + 104 * (v b4 - (pow2 26 - 1)));
    distributivity_sub_right (pow2 26) (v b1) (pow2 26 - 1);
    distributivity_sub_right (pow2 52) (v b2) (pow2 26 - 1);
    distributivity_sub_right (pow2 78) (v b3) (pow2 26 - 1);
    distributivity_sub_right (pow2 104) (v b4) (pow2 26 - 1);
    cut (res = v b0 + pow2 26 * v b1 + pow2 52 * v b2 + pow2 78 * v b3 + pow2 104 * v b4
      - (pow2 26 - 5 + pow2 26 * (pow2 26 - 1) + pow2 52 * (pow2 26 - 1)
         + pow2 78 * (pow2 26 - 1) + pow2 104 * (pow2 26 - 1)));
    assert_norm ((pow2 26 - 5 + pow2 26 * (pow2 26 - 1) + pow2 52 * (pow2 26 - 1)
         + pow2 78 * (pow2 26 - 1) + pow2 104 * (pow2 26 - 1)) = pow2 130 - 5);
    cut (res0 = res + 1 * (pow2 130 - 5));
    Math.Lemmas.lemma_mod_plus res 1 (pow2 130 - 5)
  )


val lemma_finalize_3:
  b0:u26 -> b1:u26 -> b2:u26 -> b3:u26 -> b4:u26 ->
  b0':U64.t -> b1':U64.t -> b2':U64.t -> b3':U64.t -> b4':U64.t ->
  mask:U64.t{v mask = 0 \/ v mask = pow2 64 - 1} ->
  Lemma
    (requires (maskPrime mask b0 b1 b2 b3 b4 /\ masked mask b0 b1 b2 b3 b4 b0' b1' b2' b3' b4'))
    (ensures  (v b0' < pow2 26 /\ v b1' < pow2 26 /\ v b2' < pow2 26 /\ v b3' < pow2 26 /\ v b4' < pow2 26))
let lemma_finalize_3 b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' mask =
  if v mask = 0 then ()
  else (assert_norm(pow2 26 > 5))


val lemma_finalize_0:
  b0:u26 -> b1:u26 -> b2:u26 -> b3:u26 -> b4:u26 ->
  b0':u26 -> b1':u26 -> b2':u26 -> b3':u26 -> b4':u26 ->
  mask:U64.t{v mask = 0 \/ v mask = pow2 64 - 1} ->
  Lemma
    (requires (maskPrime mask b0 b1 b2 b3 b4 /\ masked mask b0 b1 b2 b3 b4 b0' b1' b2' b3' b4'))
    (ensures  ((v b0 + pow2 26 * v b1 + pow2 52 * v b2 + pow2 78 * v b3 + pow2 104 * v b4) % (pow2 130 - 5) = (v b0' + pow2 26 * v b1' + pow2 52 * v b2' + pow2 78 * v b3' + pow2 104 * v b4')))
let lemma_finalize_0 b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' mask =
  lemma_finalize_1 b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' mask;
  lemma_finalize_2 b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' mask;
  Math.Lemmas.modulo_lemma (v b0' + pow2 26 * v b1' + pow2 52 * v b2' + pow2 78 * v b3' + pow2 104 * v b4') (pow2 130 - 5)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val lemma_eval_5: h:HyperStack.mem -> b:bigint{live h b} -> Lemma
  (eval h b 5 = v (get h b 0) + pow2 26 * v (get h b 1) + pow2 52 * v (get h b 2) + pow2 78 * v (get h b 3) + pow2 104 * v (get h b 4))
let lemma_eval_5 h b =
  assert_norm(pow2 0 = 1);
  bitweight_def templ 4;
  bitweight_def templ 3;
  bitweight_def templ 2;
  bitweight_def templ 1;
  bitweight_def templ 0;
  eval_def h b 5;
  eval_def h b 4;
  eval_def h b 3;
  eval_def h b 2;
  eval_def h b 1;
  eval_def h b 0


val lemma_norm_5: h:HyperStack.mem -> b:bigint{live h b} -> Lemma
  (requires (v (get h b 0) < pow2 26 /\ v (get h b 1) < pow2 26 /\ v (get h b 2) < pow2 26 /\ v (get h b 3) < pow2 26 /\ v (get h b 4) < pow2 26))
  (ensures  (norm h b))
let lemma_norm_5 h b = ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val lemma_finalize:
  h:HyperStack.mem ->
  b:bigint{norm h b} ->
  h':HyperStack.mem ->
  b':bigint{live h' b'} ->
  mask:U64.t{v mask = 0 \/ v mask = pow2 64 - 1} ->
  Lemma
    (requires (
      let b0 = (get h b 0) in let b1 = (get h b 1) in let b2 = (get h b 2) in
      let b3 = (get h b 3) in let b4 = (get h b 4) in
      let b0' = (get h' b' 0) in let b1' = (get h' b' 1) in let b2' = (get h' b' 2) in
      let b3' = (get h' b' 3) in let b4' = (get h' b' 4) in
      maskPrime mask b0 b1 b2 b3 b4 /\ masked mask b0 b1 b2 b3 b4 b0' b1' b2' b3' b4'))
    (ensures  (eval h' b' 5 = eval h b 5 % (pow2 130 - 5) /\ norm h' b'))
let lemma_finalize h b h' b' mask =
  let b0 = (get h b 0) in let b1 = (get h b 1) in let b2 = (get h b 2) in
  let b3 = (get h b 3) in let b4 = (get h b 4) in
  let b0' = (get h' b' 0) in let b1' = (get h' b' 1) in let b2' = (get h' b' 2) in
  let b3' = (get h' b' 3) in let b4' = (get h' b' 4) in
  lemma_eval_5 h b;
  lemma_eval_5 h' b';
  lemma_finalize_3 b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' mask;
  lemma_finalize_0 b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' mask
