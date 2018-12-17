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
module Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part4

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

module U64 = FStar.UInt64

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

let isCarried (h0:mem) (h1:mem) (b:bigint) : GTot Type0 =
  live h0 b /\ live h1 b /\ length b >= norm_length+1
  /\ (
      let b0 = v (get h0 b 0) in
      let b1 = v (get h0 b 1) in
      let b2 = v (get h0 b 2) in
      let b3 = v (get h0 b 3) in
      let b4 = v (get h0 b 4) in
      let r0  = b0 / pow2 26 in
      let r1  = (b1 + r0) / pow2 26 in
      let r2  = (b2 + r1) / pow2 26 in
      let r3  = (b3 + r2) / pow2 26 in
      v (get h1 b 5) = (b4 + r3) / pow2 26
      /\ v (get h1 b 0) = b0 % pow2 26
      /\ v (get h1 b 1) = (b1 + r0)  % pow2 26
      /\ v (get h1 b 2) = (b2 + r1)  % pow2 26
      /\ v (get h1 b 3) = (b3 + r2)  % pow2 26
      /\ v (get h1 b 4) = (b4 + r3)  % pow2 26
    )

#reset-options "--z3rlimit 10000 --initial_fuel 4 --max_fuel 4"


let u633 = x:U64.t{v x < pow2 63}


let isCarried_
  (h1:mem)
  (b0:U64.t) (b1:U64.t) (b2:U64.t) (b3:U64.t) (b4:U64.t)
  (b:bigint) : GTot Type0 =
  live h1 b /\ length b >= norm_length+1
  /\ (
      let r0  = v b0 / pow2 26 in
      let r1  = (v b1 + r0) / pow2 26 in
      let r2  = (v b2 + r1) / pow2 26 in
      let r3  = (v b3 + r2) / pow2 26 in
      v (get h1 b 5) = (v b4 + r3) / pow2 26
      /\ v (get h1 b 0) = v b0 % pow2 26
      /\ v (get h1 b 1) = (v b1 + r0)  % pow2 26
      /\ v (get h1 b 2) = (v b2 + r1)  % pow2 26
      /\ v (get h1 b 3) = (v b3 + r2)  % pow2 26
      /\ v (get h1 b 4) = (v b4 + r3)  % pow2 26
    )

#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

let carried_1 (h:mem) (b:bigint) : GTot Type0 =
  live h b /\ length b >= norm_length+1
  /\ v (get h b 0) < pow2 26
  /\ v (get h b 1) < pow2 26
  /\ v (get h b 2) < pow2 26
  /\ v (get h b 3) < pow2 26
  /\ v (get h b 4) < pow2 26
  /\ v (get h b 5) <= pow2 38


let lemma_carry_10_0 (x:int) (y:pos) : Lemma (x % y < y) = ()
let lemma_carry_10_1 (x:nat) (y:nat) (z:pos) : Lemma (requires (x < y)) (ensures (x / z <= y / z))
  = lemma_div_mod x z;
    lemma_div_mod y z;
    assert(x = z * (x / z) + x % z);
    assert(y = z * (y / z) + y % z);
    let xz = x/z in let yz = y/z in
    distributivity_sub_right z yz xz;
    assert(z * (yz - xz) + y % z - x % z > 0);
    cut (x % z < z /\ y % z < z);
    assert(z * (yz - xz) > x % z - y % z);
    assert(z * (yz - xz) > - z)
let lemma_carry_10_2 (x:nat) : Lemma (requires (x < pow2 64)) (ensures (x / pow2 26 <= pow2 38))
  = pow2_minus 64 26;
    lemma_carry_10_1 x (pow2 64) (pow2 26)


val lemma_carry_10:
  h0:mem -> h1:mem ->
  b:bigint{length b >= norm_length+1} ->
  Lemma (requires (bound63 h0 b /\ isCarried h0 h1 b))
	(ensures  (carried_1 h1 b))
let lemma_carry_10 h0 h1 b =
  let (p26:pos) = pow2 26 in
  let b0 = v (get h0 b 0) in
  let b1 = v (get h0 b 1) in
  let b2 = v (get h0 b 2) in
  let b3 = v (get h0 b 3) in
  let b4 = v (get h0 b 4) in
  nat_over_pos_is_nat b0 p26;
  let r0  = b0 / p26 in
  nat_over_pos_is_nat (b1+r0) p26;
  let r1  = (b1 + r0) / p26 in
  nat_over_pos_is_nat (b2+r1) p26;
  let r2  = (b2 + r1) / p26 in
  nat_over_pos_is_nat (b3+r2) p26;
  let r3  = (b3 + r2) / p26 in
  nat_over_pos_is_nat (b4+r3) p26;
  lemma_carry_10_0 b0 (p26);
  lemma_carry_10_0 (b1+r0) (p26);
  lemma_carry_10_0 (b2+r1) (p26);
  lemma_carry_10_0 (b3+r2) (p26);
  lemma_carry_10_0 (b4+r3) (p26);
  pow2_double_sum 63;
  pow2_lt_compat 63 26;
  pow2_lt_compat 63 38;
  lemma_carry_10_2 b0;
  lemma_carry_10_2 (b1+r0);
  lemma_carry_10_2 (b2+r1);
  lemma_carry_10_2 (b3+r2);
  lemma_carry_10_2 (b4+r3)


#reset-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

let lemma_carry_110_0 (x:int) (y:int) (z:nat) :
  Lemma (pow2 z * (x + pow2 26 * y) = pow2 z * x + pow2 (z+26) * y)
  = distributivity_add_right (pow2 z) x (pow2 26 * y);
    pow2_plus 26 z

val lemma_carry_1101:
  b0:nat -> b1:nat -> b2:nat -> b3:nat -> b4:nat ->
  c0:nat -> c1:nat -> c2:nat -> c3:nat -> c4:nat -> c5:nat ->
  Lemma (requires (
    let p26 = pow2 26 in
    c0 = (b0 % p26)
    /\ c1 = ((b0 / p26 + b1) % p26)
    /\ (b0 / p26 + b1) >= 0
    /\ c2 = (((b0 / p26 + b1) / p26 + b2) % p26)
    /\ ((b0 / p26 + b1) / p26 + b2) >= 0
    /\ c3 = ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) % p26)
    /\ (((b0 / p26 + b1) / p26 + b2) / p26 + b3) >= 0
    /\ c4 = (((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) % pow2 26)
    /\ ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) >= 0
    /\ c5 = (((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) / pow2 26) ))
    (ensures  (let p26 = pow2 26 in pow2 104 * c4 + pow2 130 * c5 = pow2 104 * ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26) + pow2 104 * b4))
let lemma_carry_1101 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5 =
  let p26 = pow2 26 in
  nat_over_pos_is_nat b0 p26;
  let r0  = b0 / p26 in
  nat_over_pos_is_nat (b1+r0) p26;
  let r1  = (b1 + r0) / p26 in
  nat_over_pos_is_nat (b2+r1) p26;
  let r2  = (b2 + r1) / p26 in
  nat_over_pos_is_nat (b3+r2) p26;
  let r3  = (b3 + r2) / p26 in
  nat_over_pos_is_nat (b4+r3) p26;
  lemma_div_mod ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) (pow2 26);
  cut (c4 + pow2 26 * c5 = (((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4);
  lemma_carry_110_0 c4 c5 104;
  cut (pow2 104 * c4 + pow2 130 * c5 = pow2 104 * (c4 + pow2 26 * c5));
  distributivity_add_right (pow2 104) ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26) b4


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_carry_1102:
  b0:nat -> b1:nat -> b2:nat -> b3:nat -> b4:nat ->
  c0:nat -> c1:nat -> c2:nat -> c3:nat -> c4:nat -> c5:nat ->
  Lemma (requires (
    let p26 = pow2 26 in
    c0 = (b0 % p26)
    /\ c1 = ((b0 / p26 + b1) % p26)
    /\ (b0 / p26 + b1) >= 0
    /\ c2 = (((b0 / p26 + b1) / p26 + b2) % p26)
    /\ ((b0 / p26 + b1) / p26 + b2) >= 0
    /\ c3 = ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) % p26)
    /\ (((b0 / p26 + b1) / p26 + b2) / p26 + b3) >= 0
    /\ c4 = (((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) % pow2 26)
    /\ ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) >= 0
    /\ c5 = (((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) / pow2 26) ))
    (ensures  (let p26 = pow2 26 in pow2 78 * c3 + pow2 104 * ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26) = pow2 78 * (((b0 / p26 + b1) / p26 + b2) / p26) + pow2 78 * b3))
let lemma_carry_1102 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5 =
  let p26 = pow2 26 in
  nat_over_pos_is_nat b0 p26;
  let r0  = b0 / p26 in
  nat_over_pos_is_nat (b1+r0) p26;
  let r1  = (b1 + r0) / p26 in
  nat_over_pos_is_nat (b2+r1) p26;
  let r2  = (b2 + r1) / p26 in
  nat_over_pos_is_nat (b3+r2) p26;
  let r3  = (b3 + r2) / p26 in
  nat_over_pos_is_nat (b4+r3) p26;
  lemma_div_mod ((((b0 / p26 + b1) / p26 + b2) / p26 + b3)) (pow2 26);
  cut (c3 + pow2 26 * ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / pow2 26) = (((b0 / p26 + b1) / p26 + b2) / p26 + b3));
  lemma_carry_110_0 c3 ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / pow2 26) 78;
  distributivity_add_right (pow2 78) (((b0 / p26 + b1) / p26 + b2) / pow2 26) b3


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_carry_1103:
  b0:nat -> b1:nat -> b2:nat -> b3:nat -> b4:nat ->
  c0:nat -> c1:nat -> c2:nat -> c3:nat -> c4:nat -> c5:nat ->
  Lemma (requires (
    let p26 = pow2 26 in
    c0 = (b0 % p26)
    /\ c1 = ((b0 / p26 + b1) % p26)
    /\ (b0 / p26 + b1) >= 0
    /\ c2 = (((b0 / p26 + b1) / p26 + b2) % p26)
    /\ ((b0 / p26 + b1) / p26 + b2) >= 0
    /\ c3 = ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) % p26)
    /\ (((b0 / p26 + b1) / p26 + b2) / p26 + b3) >= 0
    /\ c4 = (((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) % pow2 26)
    /\ ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) >= 0
    /\ c5 = (((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) / pow2 26) ))
    (ensures  (let p26 = pow2 26 in pow2 52 * c2 + pow2 78 * (((b0 / p26 + b1) / p26 + b2) / p26) = pow2 52 * ((b0 / p26 + b1) / p26) + pow2 52 * b2))
let lemma_carry_1103 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5 =
  let p26 = pow2 26 in
  nat_over_pos_is_nat b0 p26;
  let r0  = b0 / p26 in
  nat_over_pos_is_nat (b1+r0) p26;
  let r1  = (b1 + r0) / p26 in
  nat_over_pos_is_nat (b2+r1) p26;
  let r2  = (b2 + r1) / p26 in
  nat_over_pos_is_nat (b3+r2) p26;
  let r3  = (b3 + r2) / p26 in
  nat_over_pos_is_nat (b4+r3) p26;
  lemma_div_mod (((b0 / p26 + b1) / p26 + b2)) (pow2 26);
  cut (c2 + pow2 26 * ((((b0 / p26 + b1) / p26 + b2) / p26)) = (((b0 / p26 + b1) / p26 + b2)));
  lemma_carry_110_0 c2 ((((b0 / p26 + b1) / p26 + b2)) / pow2 26) 52;
  distributivity_add_right (pow2 52) (((b0 / p26 + b1) / p26)) b2


#reset-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

val lemma_carry_1104:
  b0:nat -> b1:nat -> b2:nat -> b3:nat -> b4:nat ->
  c0:nat -> c1:nat -> c2:nat -> c3:nat -> c4:nat -> c5:nat ->
  Lemma (requires (
    let p26 = pow2 26 in
    c0 = (b0 % p26)
    /\ c1 = ((b0 / p26 + b1) % p26)
    /\ (b0 / p26 + b1) >= 0
    /\ c2 = (((b0 / p26 + b1) / p26 + b2) % p26)
    /\ ((b0 / p26 + b1) / p26 + b2) >= 0
    /\ c3 = ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) % p26)
    /\ (((b0 / p26 + b1) / p26 + b2) / p26 + b3) >= 0
    /\ c4 = (((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) % pow2 26)
    /\ ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) >= 0
    /\ c5 = (((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) / pow2 26) ))
    (ensures  (let p26 = pow2 26 in pow2 26 * c1 + pow2 52 * (((b0 / p26 + b1) / p26)) = pow2 26 * ((b0 / p26)) + pow2 26 * b1))
let lemma_carry_1104 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5 =
  let p26 = pow2 26 in
  nat_over_pos_is_nat b0 p26;
  let r0  = b0 / p26 in
  nat_over_pos_is_nat (b1+r0) p26;
  let r1  = (b1 + r0) / p26 in
  nat_over_pos_is_nat (b2+r1) p26;
  let r2  = (b2 + r1) / p26 in
  nat_over_pos_is_nat (b3+r2) p26;
  let r3  = (b3 + r2) / p26 in
  nat_over_pos_is_nat (b4+r3) p26;
  lemma_div_mod (((b0 / p26 + b1))) (pow2 26);
  cut (c1 + pow2 26 * ((((b0 / p26 + b1) / p26))) = (((b0 / p26 + b1))));
  lemma_carry_110_0 c1 ((((b0 / p26 + b1))) / pow2 26) 26;
  distributivity_add_right (pow2 26) (((b0 / p26))) b1


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_carry_110:
  b0:nat -> b1:nat -> b2:nat -> b3:nat -> b4:nat ->
  c0:nat -> c1:nat -> c2:nat -> c3:nat -> c4:nat -> c5:nat ->
  Lemma (requires (
    let p26 = pow2 26 in
    c0 = (b0 % p26)
    /\ c1 = ((b0 / p26 + b1) % p26)
    /\ (b0 / p26 + b1) >= 0
    /\ c2 = (((b0 / p26 + b1) / p26 + b2) % p26)
    /\ ((b0 / p26 + b1) / p26 + b2) >= 0
    /\ c3 = ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) % p26)
    /\ (((b0 / p26 + b1) / p26 + b2) / p26 + b3) >= 0
    /\ c4 = (((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) % pow2 26)
    /\ ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) >= 0
    /\ c5 = (((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) / pow2 26) ))
    (ensures  (b0 + pow2 26 * b1 + pow2 52 * b2 + pow2 78 * b3 + pow2 104 * b4
      = c0 + pow2 26 * c1 + pow2 52 * c2 + pow2 78 * c3 + pow2 104 * c4 + pow2 130 * c5))
let lemma_carry_110 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5 =
  let p26 = pow2 26 in
  lemma_carry_1101 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5;
  let z = c0 + pow2 26 * c1 + pow2 52 * c2 + pow2 78 * c3 + pow2 104 * c4 + pow2 130 * c5 in
  cut (z = c0 + pow2 26 * c1 + pow2 52 * c2 + pow2 78 * c3 + pow2 104 * ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26) + pow2 104 * b4);
  lemma_carry_1102 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5;
  cut (c0 + pow2 26 * c1 + pow2 52 * c2 + pow2 78 * c3 + pow2 104 * ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26) + pow2 104 * b4 = c0 + pow2 26 * c1 + pow2 52 * c2 + pow2 78 * (((b0 / p26 + b1) / p26 + b2) / p26) + pow2 78 * b3 + pow2 104 * b4);
  lemma_carry_1103 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5;
  cut (c0 + pow2 26 * c1 + pow2 52 * c2 + pow2 78 * (((b0 / p26 + b1) / p26 + b2) / p26) + pow2 78 * b3 + pow2 104 * b4 = c0 + pow2 26 * c1 + pow2 52 * ((b0 / p26 + b1) / p26) + pow2 52 * b2 + pow2 78 * b3 + pow2 104 * b4);
  lemma_carry_1104 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5;
  cut (c0 + pow2 26 * c1 + pow2 52 * ((b0 / p26 + b1) / p26) + pow2 52 * b2 + pow2 78 * b3 + pow2 104 * b4 = c0 + pow2 26 * ((b0 / p26)) + pow2 26 * b1 + pow2 52 * b2 + pow2 78 * b3 + pow2 104 * b4);
  lemma_div_mod b0 (pow2 26)


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_carry_11:
  h0:mem -> h1:mem ->
  b:bigint{length b >= norm_length+1} ->
  Lemma (requires ((* bound63 h0 b /\  *)isCarried h0 h1 b))
	(ensures  ((* bound63 h0 b /\  *)isCarried h0 h1 b
	  /\ eval h1 b (norm_length+1) = eval h0 b norm_length))
let lemma_carry_11 h0 h1 b =
  let (p26:pos) = pow2 26 in
  lemma_eval_bigint_5 h0 b;
  lemma_eval_bigint_6 h1 b;
  let b0 = v (get h0 b 0) in
  let b1 = v (get h0 b 1) in
  let b2 = v (get h0 b 2) in
  let b3 = v (get h0 b 3) in
  let b4 = v (get h0 b 4) in
  nat_over_pos_is_nat b0 p26;
  let r0  = b0 / p26 in
  nat_over_pos_is_nat (b1+r0) p26;
  let r1  = (b1 + r0) / p26 in
  nat_over_pos_is_nat (b2+r1) p26;
  let r2  = (b2 + r1) / p26 in
  nat_over_pos_is_nat (b3+r2) p26;
  let r3  = (b3 + r2) / p26 in
  nat_over_pos_is_nat (b4+r3) p26;
  cut(eval h1 b 6 = v (get h1 b 0) + pow2 26  * v (get h1 b 1) + pow2 52  * v (get h1 b 2)
	       + pow2 78  * v (get h1 b 3) + pow2 104 * v (get h1 b 4) + pow2 130 * v (get h1 b 5));
  cut (v (get h1 b 0) = b0 % p26);
  cut (v (get h1 b 1) = ((b0 / p26 + b1) % p26));
  cut (v (get h1 b 2) = (((b0 / p26 + b1) / p26 + b2) % p26));
  cut (v (get h1 b 3) = ((((b0 / p26 + b1) / p26 + b2) / p26 + b3) % p26));
  cut (v (get h1 b 4) = (((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) % pow2 26) );
  cut (v (get h1 b 5) = (((((b0 / p26 + b1) / p26 + b2) / p26 + b3) / p26 + b4) / pow2 26) );
  lemma_carry_110 b0 b1 b2 b3 b4 (v (get h1 b 0)) (v (get h1 b 1)) (v (get h1 b 2)) (v (get h1 b 3)) (v (get h1 b 4)) (v (get h1 b 5))


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_carry_1:
  h0:mem -> h1:mem ->
  b:bigint{length b >= norm_length+1} ->
  Lemma (requires (bound63 h0 b /\ isCarried h0 h1 b))
	(ensures  (bound63 h0 b /\ isCarried h0 h1 b
	  /\ eval h1 b (norm_length+1) = eval h0 b norm_length
	  /\ carried_1 h1 b))
let lemma_carry_1 h0 h1 b =
  lemma_carry_10 h0 h1 b;
  lemma_carry_11 h0 h1 b


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

let carried_2 (h:mem) (b:bigint) : GTot Type0 =
  live h b /\ length b >= norm_length+1
  /\ v (get h b 0) < pow2 42
  /\ v (get h b 1) < pow2 26
  /\ v (get h b 2) < pow2 26
  /\ v (get h b 3) < pow2 26
  /\ v (get h b 4) < pow2 26


let carried_3 (h:mem) (b:bigint) : GTot Type0 =
  norm h b /\ length b >= norm_length+1
  /\ v (get h b 5) <= 1
  /\ (v (get h b 5) = 1
    ==> (v (get h b 1) < pow2 16 /\ v (get h b 2) < pow2 16  /\ v (get h b 3) < pow2 16
	/\ v (get h b 4) < pow2 16))

val lemma_div_lt: a:nat -> n:nat -> m:nat{m <= n} ->
  Lemma (requires (a < pow2 n))
	(ensures  (a / pow2 m < pow2 (n-m)))
let lemma_div_lt a n m =
  lemma_div_mod a (pow2 m);
  assert(a = pow2 m * (a / pow2 m) + a % pow2 m);
  pow2_plus m (n-m);
  assert(pow2 n = pow2 m * pow2 (n - m))

val lemma_div_rest: a:nat -> m:nat -> n:nat{m < n} ->
  Lemma (requires (a >= pow2 n /\ a < pow2 m + pow2 n))
	(ensures  (a % pow2 n < pow2 m))
let lemma_div_rest a m n =
  pow2_double_sum n;
  lemma_div_mod a (pow2 n)

let lemma_mod_0 (a:nat) (b:pos) : Lemma (a % b < b) = ()


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_carry_20:
  h0:mem -> h1:mem ->
  b:bigint{length b >= norm_length+1} ->
  Lemma (requires (carried_2 h0 b /\ isCarried h0 h1 b))
	(ensures  (carried_2 h0 b /\ isCarried h0 h1 b /\ carried_3 h1 b))
let lemma_carry_20 h0 h1 b =
  let p26 = pow2 26 in
  let b0 = v (get h0 b 0) in
  let b1 = v (get h0 b 1) in
  let b2 = v (get h0 b 2) in
  let b3 = v (get h0 b 3) in
  let b4 = v (get h0 b 4) in
  nat_over_pos_is_nat b0 p26;
  let r0  = b0 / p26 in
  nat_over_pos_is_nat (b1+r0) p26;
  let r1  = (b1 + r0) / p26 in
  nat_over_pos_is_nat (b2+r1) p26;
  let r2  = (b2 + r1) / p26 in
  nat_over_pos_is_nat (b3+r2) p26;
  let r3  = (b3 + r2) / p26 in
  nat_over_pos_is_nat (b4+r3) p26;
  lemma_carry_10_1 b0 (pow2 42) (pow2 26);
  lemma_div_lt b0 42 26;
  assert(r0 < pow2 16);
  pow2_lt_compat 26 16;
  pow2_double_sum 26;
  lemma_div_lt (b1+r0) 27 26;
  pow2_lt_compat 26 1;
  lemma_div_lt (b2+r1) 27 26;
  pow2_lt_compat 26 1;
  lemma_div_lt (b3+r2) 27 26;
  pow2_lt_compat 26 1;
  lemma_div_lt (b4+r3) 27 26;
  pow2_lt_compat 26 1;
  assert_norm(pow2 1 = 2);
  cut (v (get h1 b 5) = 1 ==> b4 + r3 >= pow2 26);
  cut (b4 + r3 >= pow2 26 ==> r3 = 1);
  cut (r3 = 1 ==> b3 + r2 >= pow2 26);
  cut (b3 + r2 >= pow2 26 ==> r1 = 1);
  cut (r1 = 1 ==> b1 + r0 >= pow2 26);
  cut (b1 + r0 >= pow2 26 ==> r0 >= 1);
  lemma_mod_0 b0 (pow2 26);
  lemma_mod_0 (b1+r0) (pow2 26);
  lemma_mod_0 (b2+r1) (pow2 26);
  lemma_mod_0 (b3+r2) (pow2 26);
  lemma_mod_0 (b4+r3) (pow2 26);
  pow2_lt_compat 16 1;
  if (v (get h1 b 5) = 1) then (
    lemma_div_rest (b1 + r0) 16 26;
    lemma_div_rest (b2 + r1) 16 26;
    lemma_div_rest (b3 + r2) 16 26;
    lemma_div_rest (b4 + r3) 16 26
  )


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_carry_2:
  h0:mem -> h1:mem ->
  b:bigint{length b >= norm_length+1} ->
  Lemma (requires (carried_2 h0 b /\ isCarried h0 h1 b))
	(ensures  (carried_2 h0 b /\ isCarried h0 h1 b
	  /\ eval h1 b (norm_length+1) = eval h0 b norm_length
	  /\ carried_3 h1 b))
let lemma_carry_2 h0 h1 b =
  lemma_carry_20 h0 h1 b;
  lemma_carry_11 h0 h1 b
