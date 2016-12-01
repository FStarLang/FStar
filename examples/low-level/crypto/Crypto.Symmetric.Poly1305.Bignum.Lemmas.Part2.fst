module Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part2

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

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private let lemma_multiplication060
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma (
    a0*b0+a0*(pow2 26*b1)+a0*(pow2 52*b2)+a0*(pow2 78*b3)+a0*(pow2 104*b4)
    = a0 * b0 + pow2 26  * (a0 * b1) + pow2 52  * (a0 * b2) + pow2 78  * (a0 * b3) + pow2 104 * (a0 * b4) )
  = ()

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

let lemma_swap p1 a p2 b : Lemma ((p1 * a) * (p2 * b) = p1 * p2 * (a * b)) = ()

private let lemma_multiplication061
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma (
    (pow2 26*a1)*b0+(pow2 26*a1)*(pow2 26*b1)+(pow2 26*a1)*(pow2 52*b2)+(pow2 26*a1)*(pow2 78*b3)+(pow2 26*a1)*(pow2 104*b4)
    = pow2 26 * (a1 * b0) + pow2 52 * (a1 * b1) + pow2 78 * (a1 * b2) + pow2 104 * (a1 * b3) + pow2 130 * (a1 * b4) )
  = pow2_plus 26 26;
    pow2_plus 26 52;
    pow2_plus 26 78;
    pow2_plus 26 104;
    lemma_swap (pow2 26) a1 (pow2 26) b1;
    lemma_swap (pow2 26) a1 (pow2 52) b2;
    lemma_swap (pow2 26) a1 (pow2 78) b3;
    lemma_swap (pow2 26) a1 (pow2 104) b4

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private let lemma_multiplication062
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma (
    (pow2 52*a2)*b0+(pow2 52*a2)*(pow2 26*b1)+(pow2 52*a2)*(pow2 52*b2)+(pow2 52*a2)*(pow2 78*b3)+(pow2 52*a2)*(pow2 104*b4)
    = pow2 52  * (a2 * b0) + pow2 78  * (a2 * b1) + pow2 104 * (a2 * b2) + pow2 130 * (a2 * b3) + pow2 156 * (a2 * b4) )
  = pow2_plus 52 26;
    pow2_plus 52 52;
    pow2_plus 52 78;
    pow2_plus 52 104;
    lemma_swap (pow2 52) a2 (pow2 26) b1;
    lemma_swap (pow2 52) a2 (pow2 52) b2;
    lemma_swap (pow2 52) a2 (pow2 78) b3;
    lemma_swap (pow2 52) a2 (pow2 104) b4

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private let lemma_multiplication063
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma (
    (pow2 78*a3)*b0+(pow2 78*a3)*(pow2 26*b1)+(pow2 78*a3)*(pow2 52*b2)+(pow2 78*a3)*(pow2 78*b3)+(pow2 78*a3)*(pow2 104*b4)
    = pow2 78  * (a3 * b0) + pow2 104 * (a3 * b1) + pow2 130 * (a3 * b2) + pow2 156 * (a3 * b3) + pow2 182 * (a3 * b4) )
  = pow2_plus 78 26;
    pow2_plus 78 52;
    pow2_plus 78 78;
    pow2_plus 78 104;
    lemma_swap (pow2 78) a3 (pow2 26) b1;
    lemma_swap (pow2 78) a3 (pow2 52) b2;
    lemma_swap (pow2 78) a3 (pow2 78) b3;
    lemma_swap (pow2 78) a3 (pow2 104) b4

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private let lemma_multiplication064
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma (
    (pow2 104*a4)*b0+(pow2 104*a4)*(pow2 26*b1)+(pow2 104*a4)*(pow2 52*b2) +(pow2 104*a4)*(pow2 78*b3)+(pow2 104*a4)*(pow2 104*b4)
    = pow2 104 * (a4 * b0) + pow2 130 * (a4 * b1) + pow2 156 * (a4 * b2) + pow2 182 * (a4 * b3) + pow2 208 * (a4 * b4) )
  = pow2_plus 104 26;
    pow2_plus 104 52;
    pow2_plus 104 78;
    pow2_plus 104 104;
    lemma_swap (pow2 104) a4 (pow2 26) b1;
    lemma_swap (pow2 104) a4 (pow2 52) b2;
    lemma_swap (pow2 104) a4 (pow2 78) b3;
    lemma_swap (pow2 104) a4 (pow2 104) b4

#reset-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0"

private let lemma_multiplication06
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma (
    a0*b0+a0*(pow2 26*b1)+a0*(pow2 52*b2)+a0*(pow2 78*b3)+a0*(pow2 104*b4)
      +(pow2 26*a1)*b0+(pow2 26*a1)*(pow2 26*b1)+(pow2 26*a1)*(pow2 52*b2)+(pow2 26*a1)*(pow2 78*b3)+(pow2 26*a1)*(pow2 104*b4)
      +(pow2 52*a2)*b0+(pow2 52*a2)*(pow2 26*b1)+(pow2 52*a2)*(pow2 52*b2)+(pow2 52*a2)*(pow2 78*b3)+(pow2 52*a2)*(pow2 104*b4)
      +(pow2 78*a3)*b0+(pow2 78*a3)*(pow2 26*b1)+(pow2 78*a3)*(pow2 52*b2)+(pow2 78*a3)*(pow2 78*b3)+(pow2 78*a3)*(pow2 104*b4)
      +(pow2 104*a4)*b0+(pow2 104*a4)*(pow2 26*b1)+(pow2 104*a4)*(pow2 52*b2) +(pow2 104*a4)*(pow2 78*b3)+(pow2 104*a4)*(pow2 104*b4)
    =              (a0 * b0) + pow2 26  * (a0 * b1) + pow2 52  * (a0 * b2) + pow2 78  * (a0 * b3) + pow2 104 * (a0 * b4)
      + pow2 26  * (a1 * b0) + pow2 52  * (a1 * b1) + pow2 78  * (a1 * b2) + pow2 104 * (a1 * b3) + pow2 130 * (a1 * b4)
      + pow2 52  * (a2 * b0) + pow2 78  * (a2 * b1) + pow2 104 * (a2 * b2) + pow2 130 * (a2 * b3) + pow2 156 * (a2 * b4)
      + pow2 78  * (a3 * b0) + pow2 104 * (a3 * b1) + pow2 130 * (a3 * b2) + pow2 156 * (a3 * b3) + pow2 182 * (a3 * b4)
      + pow2 104 * (a4 * b0) + pow2 130 * (a4 * b1) + pow2 156 * (a4 * b2) + pow2 182 * (a4 * b3) + pow2 208 * (a4 * b4) )
  = lemma_multiplication060 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4;
    lemma_multiplication061 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4;
    lemma_multiplication062 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4;
    lemma_multiplication063 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4;
    lemma_multiplication064 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private let lemma_multiplication07
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma ((a0 + pow2 26 * a1 + pow2 52 * a2 + pow2 78 * a3 + pow2 104 * a4)
    * (b0 + pow2 26 * b1 + pow2 52 * b2 + pow2 78 * b3 + pow2 104 * b4)
    =              (a0 * b0) + pow2 26  * (a0 * b1) + pow2 52  * (a0 * b2) + pow2 78  * (a0 * b3) + pow2 104 * (a0 * b4)
      + pow2 26  * (a1 * b0) + pow2 52  * (a1 * b1) + pow2 78  * (a1 * b2) + pow2 104 * (a1 * b3) + pow2 130 * (a1 * b4)
      + pow2 52  * (a2 * b0) + pow2 78  * (a2 * b1) + pow2 104 * (a2 * b2) + pow2 130 * (a2 * b3) + pow2 156 * (a2 * b4)
      + pow2 78  * (a3 * b0) + pow2 104 * (a3 * b1) + pow2 130 * (a3 * b2) + pow2 156 * (a3 * b3) + pow2 182 * (a3 * b4)
      + pow2 104 * (a4 * b0) + pow2 130 * (a4 * b1) + pow2 156 * (a4 * b2) + pow2 182 * (a4 * b3) + pow2 208 * (a4 * b4) )
  = lemma_multiplication05 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4;
    lemma_multiplication06 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private let lemma_multiplication08
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma (
    a0 * b0 + pow2 26  * (a1 * b0 + a0 * b1)
	    + pow2 52  * (a2 * b0 + a1 * b1 + a0 * b2)
	    + pow2 78  * (a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3)
	    + pow2 104 * (a4 * b0 + a3 * b1 + a2 * b2 + a1 * b3 + a0 * b4)
	    + pow2 130 * (a4 * b1 + a3 * b2 + a2 * b3 + a1 * b4)
	    + pow2 156 * (a4 * b2 + a3 * b3 + a2 * b4)
	    + pow2 182 * (a4 * b3 + a3 * b4)
	    + pow2 208 * (a4 * b4)
    =              (a0 * b0) + pow2 26  * (a0 * b1) + pow2 52  * (a0 * b2) + pow2 78  * (a0 * b3) + pow2 104 * (a0 * b4)
      + pow2 26  * (a1 * b0) + pow2 52  * (a1 * b1) + pow2 78  * (a1 * b2) + pow2 104 * (a1 * b3) + pow2 130 * (a1 * b4)
      + pow2 52  * (a2 * b0) + pow2 78  * (a2 * b1) + pow2 104 * (a2 * b2) + pow2 130 * (a2 * b3) + pow2 156 * (a2 * b4)
      + pow2 78  * (a3 * b0) + pow2 104 * (a3 * b1) + pow2 130 * (a3 * b2) + pow2 156 * (a3 * b3) + pow2 182 * (a3 * b4)
      + pow2 104 * (a4 * b0) + pow2 130 * (a4 * b1) + pow2 156 * (a4 * b2) + pow2 182 * (a4 * b3) + pow2 208 * (a4 * b4) )
  = lemma_multiplication00 (pow2 26) (a1 * b0) (a0 * b1);
    lemma_multiplication01 (pow2 52) (a2 * b0) (a1 * b1) (a0 * b2);
    lemma_multiplication02 (pow2 78) (a3 * b0) (a2 * b1) (a1 * b2) (a0 * b3);
    lemma_multiplication03 (pow2 104) (a4 * b0) (a3 * b1) (a2 * b2) (a1 * b3) (a0 * b4);
    lemma_multiplication02 (pow2 130) (a4 * b1) (a3 * b2) (a2 * b3) (a1 * b4);
    lemma_multiplication01 (pow2 156) (a4 * b2) (a3 * b3) (a2 * b4);
    lemma_multiplication00 (pow2 182) (a4 * b3) (a3 * b4)


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private let lemma_multiplication0
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int) :
  Lemma (
    (a0 + pow2 26 * a1 + pow2 52 * a2 + pow2 78 * a3 + pow2 104 * a4)
    * (b0 + pow2 26 * b1 + pow2 52 * b2 + pow2 78 * b3 + pow2 104 * b4) =
    a0 * b0 + pow2 26  * (a1 * b0 + a0 * b1)
	    + pow2 52  * (a2 * b0 + a1 * b1 + a0 * b2)
	    + pow2 78  * (a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3)
	    + pow2 104 * (a4 * b0 + a3 * b1 + a2 * b2 + a1 * b3 + a0 * b4)
	    + pow2 130 * (a4 * b1 + a3 * b2 + a2 * b3 + a1 * b4)
	    + pow2 156 * (a4 * b2 + a3 * b3 + a2 * b4)
	    + pow2 182 * (a4 * b3 + a3 * b4)
	    + pow2 208 * (a4 * b4) )
  = lemma_multiplication07 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4;
    lemma_multiplication08 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_multiplication1:
  h0:mem -> h1:mem ->
  c:bigint{length c >= 2*norm_length-1} ->
  a:bigint -> b:bigint ->
  Lemma (requires (isMultiplication h0 h1 a b c))
	(ensures  (isMultiplication h0 h1 a b c
	  /\ eval h1 c (2*norm_length-1) = eval h0 a norm_length * eval h0 b norm_length))
let lemma_multiplication1 h0 h1 c a b =
  let a0 = v (get h0 a 0) in
  let a1 = v (get h0 a 1) in
  let a2 = v (get h0 a 2) in
  let a3 = v (get h0 a 3) in
  let a4 = v (get h0 a 4) in
  let b0 = v (get h0 b 0) in
  let b1 = v (get h0 b 1) in
  let b2 = v (get h0 b 2) in
  let b3 = v (get h0 b 3) in
  let b4 = v (get h0 b 4) in
  lemma_eval_bigint_9 h1 c;
  lemma_eval_bigint_5 h0 a;
  lemma_eval_bigint_5 h0 b;
  lemma_multiplication0 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4


#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

let lemma_mul_ineq (a:nat) (b:nat) c d : Lemma (requires (a < c /\ b < d))
					    (ensures  (a * b < c * d))
  = ()

val lemma_multiplication2:
  h0:mem -> h1:mem ->
  c:bigint{length c >= 2*norm_length-1} ->
  a:bigint -> b:bigint ->
  Lemma (requires (bound27 h0 a /\ norm h0 b /\ isMultiplication h0 h1 a b c))
	(ensures  (bound27 h0 a /\ norm h0 b /\ isMultiplication h0 h1 a b c
	  /\ maxValue h1 c 9 <= norm_length * pow2 53))
let lemma_multiplication2 h0 h1 c a b =
  pow2_plus 27 26;
  let a0 = v (get h0 a 0) in
  let a1 = v (get h0 a 1) in
  let a2 = v (get h0 a 2) in
  let a3 = v (get h0 a 3) in
  let a4 = v (get h0 a 4) in
  let b0 = v (get h0 b 0) in
  let b1 = v (get h0 b 1) in
  let b2 = v (get h0 b 2) in
  let b3 = v (get h0 b 3) in
  let b4 = v (get h0 b 4) in
  lemma_mul_ineq a0 b0 (pow2 27) (pow2 26);
  lemma_mul_ineq a0 b1 (pow2 27) (pow2 26);
  lemma_mul_ineq a0 b2 (pow2 27) (pow2 26);
  lemma_mul_ineq a0 b3 (pow2 27) (pow2 26);
  lemma_mul_ineq a0 b4 (pow2 27) (pow2 26);
  lemma_mul_ineq a1 b0 (pow2 27) (pow2 26);
  lemma_mul_ineq a1 b1 (pow2 27) (pow2 26);
  lemma_mul_ineq a1 b2 (pow2 27) (pow2 26);
  lemma_mul_ineq a1 b3 (pow2 27) (pow2 26);
  lemma_mul_ineq a1 b4 (pow2 27) (pow2 26);
  lemma_mul_ineq a2 b0 (pow2 27) (pow2 26);
  lemma_mul_ineq a2 b1 (pow2 27) (pow2 26);
  lemma_mul_ineq a2 b2 (pow2 27) (pow2 26);
  lemma_mul_ineq a2 b3 (pow2 27) (pow2 26);
  lemma_mul_ineq a2 b4 (pow2 27) (pow2 26);
  lemma_mul_ineq a3 b0 (pow2 27) (pow2 26);
  lemma_mul_ineq a3 b1 (pow2 27) (pow2 26);
  lemma_mul_ineq a3 b2 (pow2 27) (pow2 26);
  lemma_mul_ineq a3 b3 (pow2 27) (pow2 26);
  lemma_mul_ineq a3 b4 (pow2 27) (pow2 26);
  lemma_mul_ineq a4 b0 (pow2 27) (pow2 26);
  lemma_mul_ineq a4 b1 (pow2 27) (pow2 26);
  lemma_mul_ineq a4 b2 (pow2 27) (pow2 26);
  lemma_mul_ineq a4 b3 (pow2 27) (pow2 26);
  lemma_mul_ineq a4 b4 (pow2 27) (pow2 26);
  assert(v (get h1 c 0) < pow2 53);
  assert(v (get h1 c 1) < 2*pow2 53);
  assert(v (get h1 c 2) < 3*pow2 53);
  assert(v (get h1 c 3) < 4*pow2 53);
  assert(v (get h1 c 4) < 5*pow2 53);
  assert(v (get h1 c 5) < 4*pow2 53);
  assert(v (get h1 c 6) < 3*pow2 53);
  assert(v (get h1 c 7) < 2*pow2 53);
  assert(v (get h1 c 8) < pow2 53);
  maxValue_bound_lemma_aux h1 c (2*norm_length-1) (5*pow2 53)


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_multiplication:
  h0:mem ->
  h1:mem ->
  c:bigint{length c >= 2*norm_length-1} ->
  a:bigint{disjoint c a} ->
  b:bigint{disjoint c b} ->
  Lemma (requires (bound27 h0 a /\ norm h0 b /\ live h1 c /\ isMultiplication h0 h1 a b c))
	(ensures  (bound27 h0 a /\ norm h0 b /\ live h1 c /\ isMultiplication h0 h1 a b c
	  /\ eval h1 c (2*norm_length-1) = eval h0 a norm_length * eval h0 b norm_length
	  /\ maxValue h1 c (2*norm_length-1) <= norm_length * pow2 53))
let lemma_multiplication h0 h1 c a b =
  lemma_multiplication1 h0 h1 c a b;
  lemma_multiplication2 h0 h1 c a b
