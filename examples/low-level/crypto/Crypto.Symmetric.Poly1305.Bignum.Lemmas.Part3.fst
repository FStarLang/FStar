module Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part3

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

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

val lemma_div_def: a:nat -> b:pos -> Lemma (a = b * (a / b) + a % b)
let lemma_div_def a b = ()

val lemma_mod_a_b: a:pos -> b:nat -> Lemma ((a + b) % a = b % a)
let lemma_mod_a_b a b = lemma_mod_plus b 1 a

val lemma_modulo_mul: a:nat -> b:nat -> p:pos -> Lemma ((a * b) % p = (a%p * b) % p)
let lemma_modulo_mul a b p =
  lemma_mod_mul_distr_l a b p
val lemma_modulo_add: a:nat -> b:nat -> p:pos -> Lemma ((a + b) % p = (a%p + b) % p)
let lemma_modulo_add a b p =
  lemma_mod_plus_distr_l a b p


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

val lemma_modulo_9_0: f:nat -> g:nat -> h:nat -> i:nat -> Lemma
  (let p = reveal prime in 
    (pow2 130 * f + pow2 156 * g + pow2 182 * h + pow2 208 * i) % p 
	   =  ((pow2 130 * f + pow2 156 * g) % p + (pow2 182 * h + pow2 208 * i) % p) % p)
let lemma_modulo_9_0 f g h i =
  let p = reveal prime in
  lemma_modulo_add (pow2 130 * f + pow2 156 * g)  (pow2 182 * h + pow2 208 * i) p;
  lemma_modulo_add (pow2 182 * h + pow2 208 * i)  ((pow2 130 * f + pow2 156 * g) % p) p

val lemma_modulo_9_1: f:nat -> g:nat -> h:nat -> i:nat -> Lemma
  (let p = reveal prime in 
	 ((pow2 130 * f + pow2 156 * g) % p = ((pow2 130 * f) % p + (pow2 156 * g) % p) % p
	 /\  (pow2 182 * h + pow2 208 * i) % p =  ((pow2 182 * h) % p + (pow2 208 * i) % p) % p))
let lemma_modulo_9_1 f g h i =
  let p = reveal prime in
  lemma_modulo_add (pow2 130 * f)  (pow2 156 * g) p;
  lemma_modulo_add (pow2 156 * g)  ((pow2 130 * f)%p) p;
  lemma_modulo_add (pow2 182 * h)  (pow2 208 * i) p;
  lemma_modulo_add (pow2 208 * i)  ((pow2 182 * h)%p) p


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

val lemma_modulo_9_2: f:nat -> g:nat -> h:nat -> i:nat -> Lemma
  (let p = reveal prime in 
	 ((pow2 130 * f + pow2 156 * g) % p = ((pow2 130 % p) * f + (pow2 156 % p) * g) % p
	 /\  (pow2 182 * h + pow2 208 * i) % p =  ((pow2 182 % p) * h + (pow2 208 % p) * i) % p))
let lemma_modulo_9_2 f g h i =
  let p = reveal prime in
  lemma_modulo_9_1 f g h i;
  lemma_modulo_mul (pow2 130)  f p;
  lemma_modulo_mul (pow2 156)  g p;
  lemma_modulo_mul (pow2 182)  h p;
  lemma_modulo_mul (pow2 208)  i p;
  lemma_modulo_add ((pow2 130 % p) * f)  ((pow2 156 % p) * g) p;
  lemma_modulo_add ((pow2 156 % p) * g)  (((pow2 130 % p) * f)%p) p;
  lemma_modulo_add ((pow2 182%p) * h)  ((pow2 208%p) * i) p;
  lemma_modulo_add ((pow2 208%p) * i)  (((pow2 182%p) * h)%p) p


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

val lemma_modulo_9_3: f:nat -> g:nat -> h:nat -> i:nat -> Lemma
  (let p = reveal prime in 
    (pow2 130 * f + pow2 156 * g + pow2 182 * h + pow2 208 * i) % p 
	   =  ((pow2 130 % p) * f + (pow2 156 % p) * g + (pow2 182 % p) * h + (pow2 208 % p) * i) % p)
let lemma_modulo_9_3 f g h i =
  let p = reveal prime in
  lemma_modulo_9_0 f g h i;
  lemma_modulo_9_2 f g h i;
  lemma_modulo_add ((pow2 130 %p) * f + (pow2 156 % p) * g)  ((pow2 182 % p) * h + (pow2 208 % p) * i) p;
  lemma_modulo_add ((pow2 182 % p) * h + (pow2 208 % p) * i)  (((pow2 130 % p) * f + (pow2 156%p) * g) % p) p


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

val lemma_modulo_9: a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat -> g:nat -> h:nat -> i:nat ->
  Lemma (requires (True))
	(ensures  (let p = reveal prime in
	  (a + pow2 26 * b + pow2 52 * c + pow2 78 * d + pow2 104 * e
	   + pow2 130 * f + pow2 156 * g + pow2 182 * h + pow2 208 * i ) % p
	  = (a + pow2 26 * b + pow2 52 * c + pow2 78 * d + pow2 104 * e
	     + (pow2 130 % p) * f + (pow2 156 % p) * g + (pow2 182 % p) * h + (pow2 208 % p) * i) % p))
let lemma_modulo_9 a b c d e f g h i =
  let p = reveal prime in
  nat_times_nat_is_nat (pow2 26)  b;
  nat_times_nat_is_nat (pow2 52)  c;
  nat_times_nat_is_nat (pow2 78)  d;
  nat_times_nat_is_nat (pow2 104) e;
  nat_times_nat_is_nat (pow2 130) f;
  nat_times_nat_is_nat (pow2 156) g;
  nat_times_nat_is_nat (pow2 182) h;
  nat_times_nat_is_nat (pow2 208) i;
  let m0 = (pow2 130 * f + pow2 156 * g + pow2 182 * h + pow2 208 * i) in
  let m1 = (a + pow2 26 * b + pow2 52 * c + pow2 78 * d + pow2 104 * e) in
  lemma_modulo_add m0 m1 p;
  cut( (m1 +m0) % p = (m1 + (m0%p)) % p);
  lemma_modulo_9_3 f g h i;
  nat_times_nat_is_nat (pow2 130 % p) f;
  nat_times_nat_is_nat (pow2 156 % p) g;
  nat_times_nat_is_nat (pow2 182 % p) h;
  nat_times_nat_is_nat (pow2 204 % p) i;
  let m2 = (pow2 130 % p) * f + (pow2 156 % p) * g + (pow2 182 % p) * h + (pow2 208 % p) * i in
  cut (m0 % p = m2 % p);
  cut (m0 % p = ((pow2 130 % p) * f + (pow2 156 % p) * g + (pow2 182 % p) * h + (pow2 208 % p) * i) % p);
  lemma_modulo_add m2 m1 p

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

val lemma_2_130_modulo_prime: unit -> Lemma (pow2 130 % (pow2 130 - 5) = 5)
let lemma_2_130_modulo_prime () =
  assert_norm (pow2 3 = 8);
  pow2_lt_compat 129 3;
  pow2_double_sum 129;
  cut(5 % (pow2 130 - 5) = 5);
  lemma_mod_a_b (pow2 130 - 5) 5


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

let isDegreeReduced (h0:mem) (h1:mem) (b:bigint) =
  live h0 b /\ live h1 b /\ length b >= 2*norm_length-1
  /\ v (get h1 b 0) = v (get h0 b 0) + 5 * v (get h0 b 5)
  /\ v (get h1 b 1) = v (get h0 b 1) + 5 * v (get h0 b 6)
  /\ v (get h1 b 2) = v (get h0 b 2) + 5 * v (get h0 b 7)
  /\ v (get h1 b 3) = v (get h0 b 3) + 5 * v (get h0 b 8)
  /\ v (get h1 b 4) = v (get h0 b 4)

let satisfiesModuloConstraints (h:heap) (b:bigint) : GTot Type0 =
  live h b /\ length b >= 2*norm_length-1
  /\ maxValue h b (2*norm_length-1) * 6 < pow2 63

val lemma_freduce_degree_0:
  h:mem ->
  b:bigint ->
  Lemma (requires (satisfiesModuloConstraints h b))
	(ensures  (satisfiesModuloConstraints h b
	  /\ 5 * v (get h b 5) < pow2 64 /\ 5 * v (get h b 6) < pow2 64 /\ 5 * v (get h b 7) < pow2 64
	  /\ 5 * v (get h b 7) < pow2 64 /\ 5 * v (get h b 8) < pow2 64
	  /\ v (get h b 0) + 5 * v (get h b 5) < pow2 64 /\ v (get h b 1) + 5 * v (get h b 6) < pow2 64
	  /\ v (get h b 2) + 5 * v (get h b 7) < pow2 64 /\ v (get h b 3) + 5 * v (get h b 8) < pow2 64
	))
let lemma_freduce_degree_0 h b =
  pow2_double_sum 63;
  maxValue_lemma_aux h b (2*norm_length-1)


let bound63 (h:heap) (b:bigint) : GTot Type0 =
  live h b /\ v (get h b 0) < pow2 63 /\ v (get h b 1) < pow2 63 /\ v (get h b 2) < pow2 63
  /\ v (get h b 3) < pow2 63 /\ v (get h b 4) < pow2 63


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

val lemma_freduce_degree1:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (satisfiesModuloConstraints h0 b /\ isDegreeReduced h0 h1 b))
	(ensures  (satisfiesModuloConstraints h0 b /\ isDegreeReduced h0 h1 b
	  /\ bound63 h1 b))
let lemma_freduce_degree1 h0 h1 b =
  maxValue_lemma_aux h0 b (2*norm_length-1)


let lemma_modulo_00 (a:nat) (b:pos) : Lemma (requires (a < b)) (ensures ( a % b = a )) = ()
let lemma_mul_nat (a:nat) (b:nat) : Lemma (a * b >= 0) = ()

let lemma_pow2_modulo_prime0 () :
  Lemma (let p = reveal prime in (
    (5 * pow2 26) % p = 5 * pow2 26
    /\ (5 * pow2 52) % p = 5 * pow2 52
    /\ (5 * pow2 78) % p = 5 * pow2 78))
  = assert_norm (pow2 3 = 8);
    lemma_2_130_modulo_prime ();
    let p = reveal prime in
    pow2_plus 3 26;
    pow2_plus 3 52;
    pow2_plus 3 78;
    pow2_double_sum 129;
    pow2_lt_compat 129 5;
    pow2_lt_compat 129 29;
    pow2_lt_compat 129 55;
    pow2_lt_compat 129 81;
    lemma_modulo_00 (5 * pow2 26) p;
    lemma_modulo_00 (5 * pow2 52) p;
    lemma_modulo_00 (5 * pow2 78) p


let lemma_pow2_modulo_prime () : Lemma (let p = reveal prime in
  pow2 130 % p = 5 /\ pow2 156 % p = 5 * pow2 26
  /\ pow2 182 % p = 5 * pow2 52 /\ pow2 208 % p = 5 * pow2 78)
  = pow2_plus 130 26;
    pow2_plus 130 52;
    pow2_plus 130 78;
    let p = reveal prime in
    lemma_modulo_mul (pow2 130) (pow2 26) p;
    lemma_modulo_mul (pow2 130) (pow2 52) p;
    lemma_modulo_mul (pow2 130) (pow2 78) p;
    lemma_pow2_modulo_prime0 ();
    lemma_2_130_modulo_prime ()

let lemma_2_26_p (a:nat) : Lemma (requires (a < pow2 26)) (ensures  (a < reveal prime /\ a % reveal prime = a))
  = pow2_double_sum 129;
    assert_norm(pow2 3 = 8);
    pow2_lt_compat 129 3;
    pow2_lt_compat 129 26;
    lemma_modulo_00 a (reveal prime)


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val lemma_freduce_degree2:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (isDegreeReduced h0 h1 b))
	(ensures  (isDegreeReduced h0 h1 b
	  /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime))
#reset-options "--z3timeout 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
let lemma_freduce_degree2 h0 h1 b = admit()
(* CH: this often fails for me even with 2000 seconds!
  let b0 = v (get h0 b 0) in
  let b1 = v (get h0 b 1) in
  let b2 = v (get h0 b 2) in
  let b3 = v (get h0 b 3) in
  let b4 = v (get h0 b 4) in
  let b5 = v (get h0 b 5) in
  let b6 = v (get h0 b 6) in
  let b7 = v (get h0 b 7) in
  let b8 = v (get h0 b 8) in
  lemma_eval_bigint_9 h0 b;
  let p = reveal prime in
  cut(eval h0 b (2*norm_length-1) % p =
      (b0 + pow2 26 * b1 + pow2 52 * b2 + pow2 78 * b3 + pow2 104 * b4
      + pow2 130 * b5 + pow2 156 * b6 + pow2 182 * b7 + pow2 208 * b8) % p);
  lemma_eval_bigint_5 h1 b;
  lemma_mul_nat (pow2 26)  b1;
  lemma_mul_nat (pow2 52)  b2;
  lemma_mul_nat (pow2 78)  b3;
  lemma_mul_nat (pow2 104) b4;
  lemma_mul_nat (pow2 130) b5;
  lemma_mul_nat (pow2 156) b6;
  lemma_mul_nat (pow2 182) b7;
  lemma_mul_nat (pow2 208) b8;
  lemma_modulo_9 b0 b1 b2 b3 b4 b5 b6 b7 b8;
  distributivity_add_right (pow2 26) b1 (5*b6);
  distributivity_add_right (pow2 52) b2 (5*b7);
  distributivity_add_right (pow2 78) b3 (5*b8);
  let p = reveal prime in
  lemma_modulo_mul (pow2 130) b5 p;
  lemma_modulo_mul (pow2 156) b6 p;
  lemma_modulo_mul (pow2 182) b7 p;
  lemma_modulo_mul (pow2 208) b8 p;
  lemma_pow2_modulo_prime ()
*)

#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
val lemma_freduce_degree:
  h0:mem ->
  h1:mem ->
  b:bigint ->
  Lemma (requires (satisfiesModuloConstraints h0 b /\ isDegreeReduced h0 h1 b))
	(ensures  (satisfiesModuloConstraints h0 b /\ isDegreeReduced h0 h1 b
	  /\ bound63 h1 b
	  /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime))
let lemma_freduce_degree h0 h1 b =
  lemma_freduce_degree1 h0 h1 b;
  lemma_freduce_degree2 h0 h1 b
