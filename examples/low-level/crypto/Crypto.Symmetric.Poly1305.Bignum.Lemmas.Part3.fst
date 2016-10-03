module Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part3

open FStar.Mul
open FStar.Ghost
(** Machine integers *)
open FStar.UInt64
(** Effects and memory layout *)
open FStar.HyperStack
open FStar.HST
(** Buffers *)
open FStar.Buffer
(** Mathematical definitions *)
open Math.Axioms
open Math.Lib
open Math.Lemmas

open Crypto.Symmetric.Poly1305.Parameters
open Crypto.Symmetric.Poly1305.Bigint
open Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part1
open Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part2

module U64 = FStar.UInt64

#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

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

#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"


let u633 = x:U64.t{v x < pow2 63}

#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"


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


let carried_1 (h:mem) (b:bigint) : GTot Type0 =
  live h b /\ length b >= norm_length+1
  /\ v (get h b 0) < pow2 26
  /\ v (get h b 1) < pow2 26
  /\ v (get h b 2) < pow2 26
  /\ v (get h b 3) < pow2 26
  /\ v (get h b 4) < pow2 26
  /\ v (get h b 5) <= pow2 38


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

let lemma_carry_10_0 (x:int) (y:pos) : Lemma (x % y < y) = ()
let lemma_carry_10_1 (x:nat) (y:nat) (z:pos) : Lemma (requires (x < y)) (ensures (x / z <= y / z))
  = assume (x / z <= y / z) (* TODO *)
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


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

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


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

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


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"


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


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

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


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

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

val lemma_carry_11:
  h0:mem -> h1:mem ->
  b:bigint{length b >= norm_length+1} ->
  Lemma (requires (bound63 h0 b /\ isCarried h0 h1 b))
	(ensures  (bound63 h0 b /\ isCarried h0 h1 b
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


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

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


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

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
    ==> (v (get h b 1) < pow2 18 /\ v (get h b 2) < pow2 18  /\ v (get h b 3) < pow2 18
	/\ v (get h b 4) < pow2 18))

val lemma_carry_20:
  h0:mem -> h1:mem ->
  b:bigint{length b >= norm_length+1} ->
  Lemma (requires (carried_2 h0 b /\ isCarried h0 h1 b))
	(ensures  (carried_2 h0 b /\ isCarried h0 h1 b /\ carried_3 h1 b))
(* let lemma_carry_20 h0 h1 b = *)
  


assume val lemma_carry_2:
  h0:mem -> h1:mem ->
  b:bigint{length b >= norm_length+1} ->
  Lemma (requires (carried_2 h0 b /\ isCarried h0 h1 b))
	(ensures  (carried_2 h0 b /\ isCarried h0 h1 b
	  /\ eval h1 b (norm_length+1) = eval h0 b norm_length
	  /\ carried_3 h1 b))

let carriedTopBottom (h0:mem) (h1:mem) (b:bigint) : GTot Type0 =
  live h0 b /\ live h1 b /\ length b >= norm_length+1
  /\ v (get h1 b 0) = v (get h0 b 0) + 5 * v (get h0 b 5)
  /\ v (get h1 b 1) = v (get h0 b 1)
  /\ v (get h1 b 2) = v (get h0 b 2)
  /\ v (get h1 b 3) = v (get h0 b 3)
  /\ v (get h1 b 4) = v (get h0 b 4)


assume val lemma_carry_top_1:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carried_1 h0 b /\ carriedTopBottom h0 h1 b))
	(ensures  (carried_1 h0 b /\ carriedTopBottom h0 h1 b
	  /\ carried_2 h1 b
	  /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime))


let carried_4 (h:mem) (b:bigint) : GTot Type0 =
  live h b /\ v (get h b 0) < pow2 26 + 5
  /\ v (get h b 1) < pow2 26
  /\ (v (get h b 0) >= pow2 26 ==> v (get h b 1) < pow2 18)
  /\ v (get h b 2) < pow2 26
  /\ v (get h b 3) < pow2 26
  /\ v (get h b 4) < pow2 26


assume val lemma_carry_top_2:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (norm h0 b /\ length b >= norm_length + 1
		  /\ v (get h0 b 5) <= 1 /\ carriedTopBottom h0 h1 b))
	(ensures  (norm h0 b /\ length b >= norm_length + 1
	  /\ v (get h0 b 5) <= 1 /\ carriedTopBottom h0 h1 b
	  /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime
	  /\ carried_4 h1 b))


let isCarried01 (h0:mem) (h1:mem) (b:bigint) =
  live h0 b /\ live h1 b
  /\ v (get h1 b 0) = v (get h0 b 0) % pow2 26
  /\ v (get h1 b 1) = v (get h0 b 1) + (v (get h0 b 0) / pow2 26)
  /\ v (get h1 b 2) = v (get h0 b 2)
  /\ v (get h1 b 3) = v (get h0 b 3)
  /\ v (get h1 b 4) = v (get h0 b 4)

assume val lemma_carry_0_to_1:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carried_4 h0 b /\ isCarried01 h0 h1 b))
	(ensures  (carried_4 h0 b /\ isCarried01 h0 h1 b
	  /\ norm h1 b /\ eval h1 b norm_length = eval h0 b norm_length))
