module Crypto.Symmetric.Poly1305.Lemmas

open FStar.Mul
open FStar.Ghost
open FStar.Seq
(** Machine integers *)
open FStar.UInt8
open FStar.UInt64
open FStar.Int.Cast
(** Effects and memory layout *)
open FStar.HyperStack
(** Buffers *)
open FStar.Buffer
(** Mathematical definitions *)
open FStar.Math.Lemmas
(** Helper functions for buffers *)
open Buffer.Utils
open Crypto.Symmetric.Bytes

module U8 = FStar.UInt8
module U64 = FStar.UInt64

#set-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"


(* JK: TODO
   Those are bitvector lemmas that need to be proven using FStar.BitVector and then go
   to FStar.UInt
   *)
assume val lemma_logor_dijoint: #n:pos -> a:UInt.uint_t n -> b:UInt.uint_t n -> m:nat{m < n} ->
  Lemma (requires (a % pow2 m = 0 /\ b < pow2 m))
        (ensures  (UInt.logor #n a b = a + b))

assume val lemma_logand_pow2_gte: #n:pos -> x:UInt.uint_t n -> y:UInt.uint_t n -> m:nat ->
       Lemma (requires (x % pow2 m = 0))
             (ensures  (UInt.logand x y % pow2 m = 0))

assume val lemma_logand_pow2_lt: #n:pos -> x:UInt.uint_t n -> y:UInt.uint_t n -> m:nat ->
       Lemma (requires (x < pow2 m))
             (ensures  (UInt.logand x y < pow2 m))

assume val lemma_logand_mask: #n:pos -> x:UInt.uint_t n -> m:nat{m <= n} ->
       Lemma (requires (True))
             (ensures  (pow2 m < pow2 n /\ UInt.logand #n x (pow2 m - 1) = x % pow2 m))


val pow2_8_lemma: n:nat ->
  Lemma
    (requires (n = 8))
    (ensures  (pow2 n = 256))
    [SMTPat (pow2 n)]
let pow2_8_lemma n = assert_norm(pow2 8 = 256)

val pow2_32_lemma: n:nat ->
  Lemma
    (requires (n = 32))
    (ensures  (pow2 n = 4294967296))
    [SMTPat (pow2 n)]
let pow2_32_lemma n = assert_norm(pow2 32 = 4294967296)

val pow2_64_lemma: n:nat ->
  Lemma
    (requires (n = 64))
    (ensures  (pow2 n = 18446744073709551616))
    [SMTPat (pow2 n)]
let pow2_64_lemma n = assert_norm(pow2 64 = 18446744073709551616)


#set-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"


val lemma_add_disjoint: #z:pos -> a:UInt.uint_t z -> b:UInt.uint_t z -> n:nat -> m:nat{m < z} -> Lemma
  (requires (a % pow2 m = 0 /\ b < pow2 m /\ a < pow2 n /\ n >= m))
  (ensures  (a + b < pow2 n))
let lemma_add_disjoint #z a b n m =
  lemma_logor_dijoint a b m;
  let c = a / pow2 m in
  Math.Lemmas.lemma_div_exact a (pow2 m);
  cut(a + b < c * pow2 m + pow2 m);
  Math.Lemmas.pow2_plus (n-m) m;
  cut(c < pow2 (n-m));
  Math.Lemmas.distributivity_add_right (pow2 m) c 1;
  cut(a + b < pow2 m * (c + 1));
  Math.Lemmas.lemma_mult_le_right (pow2 m) (c+1) (pow2 (n-m))


#set-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

private val mk_mask: nbits:FStar.UInt32.t{FStar.UInt32.v nbits < 64} ->
  Tot (z:U64.t{v z == pow2 (FStar.UInt32.v nbits) - 1})
let mk_mask nbits =
  Math.Lemmas.pow2_lt_compat 64 (FStar.UInt32.v nbits);
  U64 ((1uL <<^ nbits) -^ 1uL)


#set-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

let u64_32 = u:U64.t{U64.v u < pow2 32}


val lemma_div_pow2_lt: x:nat -> n:nat -> m:nat{m <= n} -> Lemma
  (requires (x < pow2 n))
  (ensures  (x / pow2 m < pow2 (n - m)))
let lemma_div_pow2_lt x n m =
  Math.Lemmas.lemma_div_mod x (pow2 m);
  Math.Lemmas.pow2_plus (m) (n-m)

module U32 = FStar.UInt32

val lemma_toField_2_0_0: n:nat{n < pow2 32} -> m:nat{m <= 26} -> Lemma
  (((n * pow2 m) % pow2 26) % pow2 m = 0)
let lemma_toField_2_0_0 n m =
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 n 26 m;
  Math.Lemmas.pow2_multiplication_modulo_lemma_1 (n % pow2 (26-m)) m m


val lemma_toField_2_0: n0:u64_32 -> n1:u64_32 -> n2:u64_32 -> n3:u64_32 -> Lemma
  (requires (True))
  (ensures  (let mask_26 = mk_mask 26ul in
    v (n0 &^ mask_26) < pow2 26
    /\ v (n0 >>^ 26ul) < pow2 6 /\ v ((n1 <<^ 6ul) &^ mask_26) % pow2 6 = 0
    /\ v ((n1 <<^ 6ul) &^ mask_26) < pow2 26
    /\ v (n1 >>^ 20ul) < pow2 12 /\ v ((n2 <<^ 12ul) &^ mask_26) % pow2 12 = 0
    /\ v ((n2 <<^ 12ul) &^ mask_26) < pow2 26
    /\ v (n2 >>^ 14ul) < pow2 18 /\ v ((n3 <<^ 18ul) &^ mask_26) % pow2 18 = 0
    /\ v ((n3 <<^ 18ul) &^ mask_26) < pow2 26
    /\ v (n3 >>^ 8ul) < pow2 24))
let lemma_toField_2_0 n0 n1 n2 n3 =
  let mask_26 = mk_mask 26ul in
  lemma_logand_mask (v (n0)) 26;
  lemma_logand_mask (v ((n1 <<^ 6ul))) 26;
  lemma_logand_mask (v ((n2 <<^ 12ul))) 26;
  lemma_logand_mask (v ((n3 <<^ 18ul))) 26;
  lemma_div_pow2_lt (v n0) 32 26;
  lemma_div_pow2_lt (v n1) 32 20;
  lemma_div_pow2_lt (v n2) 32 14;
  lemma_div_pow2_lt (v n3) 32  8;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v n1 * pow2 6) 26 64;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v n2 * pow2 12) 26 64;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v n3 * pow2 18) 26 64;
  lemma_toField_2_0_0 (v n1) 6;
  lemma_toField_2_0_0 (v n2) 12;
  lemma_toField_2_0_0 (v n3) 18


val lemma_div_pow2_mod: a:nat -> m:nat -> n:nat ->
  Lemma (requires (a < pow2 m /\ n <= m))
        (ensures  (n <= m /\ (a / pow2 n) % pow2 (m-n) = a/pow2 n))
let lemma_div_pow2_mod a m n =
  lemma_div_pow2_lt a m n; Math.Lemmas.modulo_lemma (a/pow2 n) (pow2 (m-n))

val lemma_toField_2_1_0: n0:u64_32 -> n1:u64_32 -> n2:u64_32 -> n3:u64_32 ->
  n0':U64.t -> n1':U64.t -> n2':U64.t -> n3':U64.t -> n4':U64.t -> Lemma
  (requires (v n0' = v n0 % pow2 26
    /\ v n1' = v n0 / pow2 26 + ((v n1 * pow2 6) % pow2 26)
    /\ v n2' = v n1 / pow2 20 + ((v n2 * pow2 12) % pow2 26)
    /\ v n3' = v n2 / pow2 14 + ((v n3 * pow2 18) % pow2 26)
    /\ v n4' = v n3 / pow2 8))
  (ensures  (v n0' + pow2 26 * v n1' + pow2 52 * v n2' + pow2 78 * v n3' + pow2 104 * v n4'
    = v n0 % pow2 26 + pow2 26 * (v n0 / pow2 26)
      + pow2 26 * ((v n1 * pow2 6) % pow2 26) + pow2 52 * (v n1 / pow2 20)
      + pow2 52 * ((v n2 * pow2 12) % pow2 26) + pow2 78 * (v n2 / pow2 14)
      + pow2 78 * ((v n3 * pow2 18) % pow2 26) + pow2 104 * (v n3 / pow2 8)))
let lemma_toField_2_1_0 n0 n1 n2 n3 n0' n1' n2' n3' n4' =
  let v0 = v n0 in let v1 = v n1 in let v2 = v n2 in let v3 = v n3 in
  let v0' = v n0' in let v1' = v n1' in let v2' = v n2' in let v3' = v n3' in let v4' = v n4' in
  let vr = v n0' + pow2 26 * v n1' + pow2 52 * v n2' + pow2 78 * v n3' + pow2 104 * v n4' in
  Math.Lemmas.lemma_div_mod v0 (pow2 26);
  Math.Lemmas.distributivity_add_right (pow2 26) (v0 / pow2 26) ((v1 * pow2 6) % pow2 26);
  Math.Lemmas.distributivity_add_right (pow2 52) (v1 / pow2 20) ((v2 * pow2 12) % pow2 26);
  Math.Lemmas.distributivity_add_right (pow2 78) (v2 / pow2 14) ((v3 * pow2 18) % pow2 26)


val lemma_toField_2_1: x:nat{x < pow2 32} -> Lemma
  (requires (True))
  (ensures  (pow2 26 * ((x * pow2 6) % pow2 26) + pow2 52 * (x / pow2 20) = pow2 32 * x))
let lemma_toField_2_1 x =
  Math.Lemmas.pow2_plus 26 6;
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 x 26 6;
  cut ((x * pow2 6) % pow2 26 = pow2 6 * (x % (pow2 20)));
  Math.Lemmas.pow2_plus 32 20;
  Math.Lemmas.lemma_div_mod x (pow2 20);
  Math.Lemmas.distributivity_add_right (pow2 32) (x % pow2 20) (pow2 20 * (x / pow2 20))


#set-options "--initial_fuel 0 --max_fuel 0 --z3timeout 10"

val lemma_toField_2_2: x:nat{x < pow2 32} -> Lemma
  (requires (True))
  (ensures  (pow2 52 * ((x * pow2 12) % pow2 26) + pow2 78 * (x / pow2 14) = pow2 64 * x))
let lemma_toField_2_2 x =
  Math.Lemmas.pow2_plus 52 12;
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 x 26 12;
  cut ((x * pow2 12) % pow2 26 = pow2 12 * (x % (pow2 14)));
  Math.Lemmas.pow2_plus 64 14;
  Math.Lemmas.lemma_div_mod x (pow2 14);
  Math.Lemmas.distributivity_add_right (pow2 64) (x % pow2 14) (pow2 14 * (x / pow2 14))


val lemma_toField_2_3: x:nat{x < pow2 32} -> Lemma
  (requires (True))
  (ensures  (pow2 78 * ((x * pow2 18) % pow2 26) + pow2 104 * (x / pow2 8) = pow2 96 * x))
let lemma_toField_2_3 x =
  Math.Lemmas.pow2_plus 78 18;
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 x 26 18;
  cut ((x * pow2 18) % pow2 26 = pow2 18 * (x % (pow2 8)));
  Math.Lemmas.pow2_plus 96 8;
  Math.Lemmas.lemma_div_mod x (pow2 8);
  Math.Lemmas.distributivity_add_right (pow2 96) (x % pow2 8) (pow2 8 * (x / pow2 8))


val lemma_toField_2_4: n0:u64_32 -> n1:u64_32 -> n2:u64_32 -> n3:u64_32 ->
  n0':U64.t -> n1':U64.t -> n2':U64.t -> n3':U64.t -> n4':U64.t -> Lemma
  (requires (v n0' = v n0 % pow2 26
    /\ v n1' = v n0 / pow2 26 + ((v n1 * pow2 6) % pow2 26)
    /\ v n2' = v n1 / pow2 20 + ((v n2 * pow2 12) % pow2 26)
    /\ v n3' = v n2 / pow2 14 + ((v n3 * pow2 18) % pow2 26)
    /\ v n4' = v n3 / pow2 8))
  (ensures  (v n0' + pow2 26 * v n1' + pow2 52 * v n2' + pow2 78 * v n3' + pow2 104 * v n4'
    == v n0 + pow2 32 * v n1 + pow2 64 * v n2 + pow2 96 * v n3))
let lemma_toField_2_4 n0 n1 n2 n3 n0' n1' n2' n3' n4' =
  let v0 = v n0 in let v1 = v n1 in let v2 = v n2 in let v3 = v n3 in
  let v0' = v n0' in let v1' = v n1' in let v2' = v n2' in let v3' = v n3' in let v4' = v n4' in
  let vr = v n0' + pow2 26 * v n1' + pow2 52 * v n2' + pow2 78 * v n3' + pow2 104 * v n4' in
  lemma_toField_2_1_0 n0 n1 n2 n3 n0' n1' n2' n3' n4';
  cut (vr = v0 % pow2 26 + pow2 26 * (v0 / pow2 26)
    + pow2 26 * ((v1 * pow2 6) % pow2 26) + pow2 52 * (v1 / pow2 20)
    + pow2 52 * ((v2 * pow2 12) % pow2 26) + pow2 78 * (v2 / pow2 14)
    + pow2 78 * ((v3 * pow2 18) % pow2 26) + pow2 104 * (v3 / pow2 8) );
  Math.Lemmas.lemma_div_mod v0 (pow2 26);
  lemma_toField_2_1 v1;
  lemma_toField_2_2 v2;
  lemma_toField_2_3 v3


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

val lemma_toField_2: n0:u64_32 -> n1:u64_32 -> n2:u64_32 -> n3:u64_32 ->
  n0':U64.t -> n1':U64.t -> n2':U64.t -> n3':U64.t -> n4':U64.t -> Lemma
  (requires (let mask_26 = mk_mask 26ul in
    n0' == (n0 &^ mask_26)
    /\ n1' == ((n0 >>^ 26ul) |^ ((n1 <<^ 6ul) &^ mask_26))
    /\ n2' == ((n1 >>^ 20ul) |^ ((n2 <<^ 12ul) &^ mask_26))
    /\ n3' == ((n2 >>^ 14ul) |^ ((n3 <<^ 18ul) &^ mask_26))
    /\ n4' == (n3 >>^ 8ul) ))
  (ensures  (v n0' + pow2 26 * v n1' + pow2 52 * v n2' + pow2 78 * v n3' + pow2 104 * v n4'
    == v n0 + pow2 32 * v n1 + pow2 64 * v n2 + pow2 96 * v n3 ))
let lemma_toField_2 n0 n1 n2 n3 n0' n1' n2' n3' n4' =
  let open FStar.UInt64 in
  let mask_26 = mk_mask 26ul in
  cut(v mask_26 = pow2 26 - 1);
  assert_norm(pow2 64 > pow2 26);
  lemma_logand_mask #64 (v n0) 26;
  lemma_toField_2_0 n0 n1 n2 n3;
  let v0_26 = v (n0 >>^ 26ul) in
  let v1_6 = v ((n1 <<^ 6ul) &^ mask_26) in
  let v1_20 = v (n1 >>^ 20ul) in
  let v2_12 = v ((n2 <<^ 12ul) &^ mask_26) in
  let v2_14 = v (n2 >>^ 14ul) in
  let v3_18 = v ((n3 <<^ 18ul) &^ mask_26) in
  let v3_8 = v (n3 >>^ 8ul) in
  lemma_logor_dijoint v1_6 v0_26 6;
  UInt.logor_commutative v1_6 v0_26;
  lemma_logor_dijoint v2_12 v1_20 12;
  UInt.logor_commutative v2_12 v1_20;
  lemma_logor_dijoint v3_18 v2_14 18;
  UInt.logor_commutative v3_18 v2_14;
  Math.Lemmas.nat_times_nat_is_nat (v n1) (pow2 6);
  Math.Lemmas.nat_times_nat_is_nat (v n2) (pow2 12);
  Math.Lemmas.nat_times_nat_is_nat (v n3) (pow2 18);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v n1 * pow2 6) 26 64;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v n2 * pow2 12) 26 64;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v n3 * pow2 18) 26 64;
  lemma_logand_mask #64 (v n0) 26;
  lemma_logand_mask #64 (v (n1 <<^ 6ul)) 26;
  lemma_logand_mask #64 (v (n2 <<^ 12ul)) 26;
  lemma_logand_mask #64 (v (n3 <<^ 18ul)) 26;
  cut (v1_6 = (v n1 * pow2 6) % pow2 26);
  cut (v n0' = v n0 % pow2 26);
  cut (v n1' = v n0 / pow2 26 + ((v n1 * pow2 6) % pow2 26));
  cut (v n2' = v n1 / pow2 20 + ((v n2 * pow2 12) % pow2 26));
  cut (v n3' = v n2 / pow2 14 + ((v n3 * pow2 18) % pow2 26));
  cut (v n4' = v n3 / pow2 8);
  lemma_toField_2_4 n0 n1 n2 n3 n0' n1' n2' n3' n4'


val lemma_mod_pow2: a:nat -> b:nat -> c:nat{c <= b} ->
  Lemma (requires (a % pow2 b = 0))
        (ensures  (a % pow2 c = 0))
let lemma_mod_pow2 a b c =
  Math.Lemmas.pow2_plus (b-c) c;
  cut (pow2 b = pow2 (b-c) * pow2 c);
  Math.Lemmas.lemma_div_exact a (pow2 b);
  let q = a / pow2 b in
  cut (a = q * pow2 b);
  cut (a = q * pow2 (b - c) * pow2 c);
  Math.Lemmas.lemma_mod_plus 0 (q * pow2 (b - c)) (pow2 c)


val lemma_disjoint_bounded:
  b0:U64.t -> b1:U64.t -> l:nat -> m:nat{m >= l} -> n:nat{n > m /\ n <= 64} ->
  Lemma (requires (U64 (v b0 < pow2 m /\ v b1 % pow2 m = 0 /\ v b1 < pow2 n /\ v b0 % pow2 l = 0)))
        (ensures  (U64 (v (b0 |^ b1) = v b0 + v b1 /\ v b0 + v b1 < pow2 n /\ (v b0 + v b1) % pow2 l = 0)))
let lemma_disjoint_bounded b0 b1 l m n =
  let open FStar.UInt64 in
  lemma_logor_dijoint (v b1) (v b0) m;
  lemma_add_disjoint (v b1) (v b0) n m;
  UInt.logor_commutative (v b0) (v b1);
  lemma_mod_pow2 (v b1) m l;
  Math.Lemmas.lemma_mod_plus_distr_l (v b0) (v b1) (pow2 l);
  Math.Lemmas.lemma_mod_plus_distr_l (v b1) ((v b0) % pow2 l) (pow2 l)

#set-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

val lemma_toField_3: n0:u64_32 -> n1:u64_32 -> n2:u64_32 -> n3:u64_32 ->
  n0':U64.t -> n1':U64.t -> n2':U64.t -> n3':U64.t -> n4':U64.t -> Lemma
  (requires (let mask_26 = mk_mask 26ul in
    n0' == (n0 &^ mask_26)
    /\ n1' == ((n0 >>^ 26ul) |^ ((n1 <<^ 6ul) &^ mask_26))
    /\ n2' == ((n1 >>^ 20ul) |^ ((n2 <<^ 12ul) &^ mask_26))
    /\ n3' == ((n2 >>^ 14ul) |^ ((n3 <<^ 18ul) &^ mask_26))
    /\ n4' == (n3 >>^ 8ul) ))
  (ensures  (U64.v n4' < pow2 24
    /\ U64.v n3' < pow2 26 /\ U64.v n2' < pow2 26 /\ U64.v n1' < pow2 26 /\ U64.v n0' < pow2 26))
let lemma_toField_3 n0 n1 n2 n3 n0' n1' n2' n3' n4' =
  let open FStar.UInt64 in
  let mask_26 = mk_mask 26ul in
  cut(v mask_26 = pow2 26 - 1);
  assert_norm(pow2 64 > pow2 26);
  assert_norm(pow2 0 = 1);
  lemma_logand_mask #64 (v n0) 26;
  lemma_toField_2_0 n0 n1 n2 n3;
  let v0_26 = v (n0 >>^ 26ul) in
  let v1_6 = v ((n1 <<^ 6ul) &^ mask_26) in
  let v1_20 = v (n1 >>^ 20ul) in
  let v2_12 = v ((n2 <<^ 12ul) &^ mask_26) in
  let v2_14 = v (n2 >>^ 14ul) in
  let v3_18 = v ((n3 <<^ 18ul) &^ mask_26) in
  let v3_8 = v (n3 >>^ 8ul) in
  lemma_logor_dijoint v1_6 v0_26 6;
  UInt.logor_commutative v1_6 v0_26;
  lemma_logor_dijoint v2_12 v1_20 12;
  UInt.logor_commutative v2_12 v1_20;
  lemma_logor_dijoint v3_18 v2_14 18;
  UInt.logor_commutative v3_18 v2_14;
  lemma_disjoint_bounded (n0 >>^ 26ul) ((n1 <<^ 6ul) &^ mask_26) 0 6 26;
  lemma_disjoint_bounded (n1 >>^ 20ul) ((n2 <<^ 12ul) &^ mask_26) 0 12 26;
  lemma_disjoint_bounded (n2 >>^ 14ul) ((n3 <<^ 18ul) &^ mask_26) 0 18 26;
  lemma_div_pow2_lt (v n3) 32 8


#set-options "--initial_fuel 1 --max_fuel 1 --z3timeout 5"

(* The little_endian function but computed from the most significant bit, makes the
   enrolling of the function to concrete values easiers for math *)
let rec little_endian_from_top (s:Seq.seq U8.t) (len:nat{len <= Seq.length s}) : GTot nat
  = if len = 0 then 0
    else pow2 (8 * (len - 1)) * U8.v (Seq.index s (len-1)) + little_endian_from_top s (len-1)


#set-options "--z3timeout 50 --initial_fuel 1 --max_fuel 1"

val lemma_little_endian_from_top_:
  s:Seq.seq U8.t{Seq.length s > 0} -> len:nat{len <= Seq.length s} ->
  Lemma (requires (True))
        (ensures  (little_endian (Seq.slice s 0 len) = little_endian_from_top s len))
let rec lemma_little_endian_from_top_ s len =
  if len = 0 then ()
  else (
    lemma_little_endian_from_top_ s (len-1);
    let s' = Seq.slice s 0 (len-1) in
    let s'' = Seq.slice s (len-1) len in
    Seq.lemma_eq_intro (Seq.slice s 0 len) (Seq.append s' s'');
    Seq.lemma_eq_intro s'' (Seq.create 1 (Seq.index s (len-1)));
    little_endian_append s' s'';
    little_endian_singleton (Seq.index s (len-1))
  )


#set-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

val lemma_little_endian_from_top:
  s:Seq.seq U8.t{Seq.length s > 0} ->
  Lemma (requires (True))
        (ensures  (little_endian s = little_endian_from_top s (Seq.length s)))
let lemma_little_endian_from_top s =
  Seq.lemma_eq_intro s (Seq.slice s 0 (Seq.length s)); lemma_little_endian_from_top_ s (Seq.length s)

#set-options "--z3timeout 5 --initial_fuel 1 --max_fuel 1"

val lemma_little_endian_from_top_def: s:Seq.seq U8.t -> len:nat{Seq.length s >= len} ->
  Lemma (requires (True))
        (ensures  ((len = 0 ==> little_endian_from_top s len = 0)
          /\ (len > 0 ==> little_endian_from_top s len = pow2 (8*(len-1)) * U8.v (Seq.index s (len-1)) + little_endian_from_top s (len-1))))
let lemma_little_endian_from_top_def s len = ()


#set-options "--initial_fuel 0 --max_fuel 0 -z3timeout 20"

val lemma_little_endian_of_u64: u:U64.t -> w:Seq.seq U8.t{Seq.length w = 4} ->
  Lemma (requires  (U64.v u == U8.v (Seq.index w 0) + pow2 8 * U8.v (Seq.index w 1) + pow2 16 * U8.v (Seq.index w 2) + pow2 24 * U8.v (Seq.index w 3)))
        (ensures   (little_endian w = U64.v u))
let lemma_little_endian_of_u64 u w =
  lemma_little_endian_from_top w;
  assert_norm (pow2 0 = 1);
  lemma_little_endian_from_top_def w 4;
  lemma_little_endian_from_top_def w 3;
  lemma_little_endian_from_top_def w 2;
  lemma_little_endian_from_top_def w 1;
  lemma_little_endian_from_top_def w 0


#set-options "--initial_fuel 0 --max_fuel 0 -z3timeout 5"

private let lemma_get_word #a (b:Buffer.buffer a) (h:HyperStack.mem{live h b}) (i:nat{i < Buffer.length b}) :
  Lemma (Seq.index (as_seq h b) i == get h b i)
  = ()

#set-options "--initial_fuel 0 --max_fuel 0 --z3timeout 40"

private let lemma_word_vals (w:Buffer.buffer U8.t{length w = 16}) (h:HyperStack.mem{live h w}) :
  Lemma (
    let s' = as_seq h w in
    let s04 = Seq.slice s' 0 4 in
    let s48 = Seq.slice s' 4 8 in
    let s812 = Seq.slice s' 8 12 in
    let s1216 = Seq.slice s' 12 16 in
    Seq.index s04 0 = get h w 0
    /\ Seq.index s04 1 = get h w 1
    /\ Seq.index s04 2 = get h w 2
    /\ Seq.index s04 3 = get h w 3
    /\ Seq.index s48 0 = get h w 4
    /\ Seq.index s48 1 = get h w 5
    /\ Seq.index s48 2 = get h w 6
    /\ Seq.index s48 3 = get h w 7
    /\ Seq.index s812 0 = get h w 8
    /\ Seq.index s812 1 = get h w 9
    /\ Seq.index s812 2 = get h w 10
    /\ Seq.index s812 3 = get h w 11
    /\ Seq.index s1216 0 = get h w 12
    /\ Seq.index s1216 1 = get h w 13
    /\ Seq.index s1216 2 = get h w 14
    /\ Seq.index s1216 3 = get h w 15
  ) =
    lemma_get_word w h 0; lemma_get_word w h 1; lemma_get_word w h 2; lemma_get_word w h 3;
    lemma_get_word w h 4; lemma_get_word w h 5; lemma_get_word w h 6; lemma_get_word w h 7;
    lemma_get_word w h 8; lemma_get_word w h 9; lemma_get_word w h 10; lemma_get_word w h 11;
    lemma_get_word w h 12; lemma_get_word w h 13; lemma_get_word w h 14; lemma_get_word w h 15;
    let s' = as_seq h w in
    cut (Seq.length s' = 16);
    let s04 = Seq.slice s' 0 4 in
    let s48 = Seq.slice s' 4 8 in
    let s812 = Seq.slice s' 8 12 in
    let s1216 = Seq.slice s' 12 16 in
    cut (Seq.index s04 0 == Seq.index s' 0);
    cut (Seq.index s04 1 == Seq.index s' 1);
    cut (Seq.index s04 2 == Seq.index s' 2);
    cut (Seq.index s04 3 == Seq.index s' 3);
    cut (Seq.index s48 0 == Seq.index s' 4);
    cut (Seq.index s48 1 == Seq.index s' 5);
    cut (Seq.index s48 2 == Seq.index s' 6);
    cut (Seq.index s48 3 == Seq.index s' 7);
    cut (Seq.index s812 0 == Seq.index s' 8);
    cut (Seq.index s812 1 == Seq.index s' 9);
    cut (Seq.index s812 2 == Seq.index s' 10);
    cut (Seq.index s812 3 == Seq.index s' 11);
    cut (Seq.index s1216 0 == Seq.index s' 12);
    cut (Seq.index s1216 1 == Seq.index s' 13);
    cut (Seq.index s1216 2 == Seq.index s' 14);
    cut (Seq.index s1216 3 == Seq.index s' 15)


private let lemma_seq_append_16_to_4 #a (s:Seq.seq a{Seq.length s = 16}) : Lemma
  (Seq.append (Seq.append (Seq.append (Seq.slice s 0 4) (Seq.slice s 4 8))
                                      (Seq.slice s 8 12))
                          (Seq.slice s 12 16) == s)
  = Seq.lemma_eq_intro (Seq.append (Seq.slice s 0 12) (Seq.slice s 12 16)) s;
    Seq.lemma_eq_intro (Seq.append (Seq.slice s 0 8) (Seq.slice s 8 12)) (Seq.slice s 0 12);
    Seq.lemma_eq_intro (Seq.append (Seq.slice s 0 4) (Seq.slice s 4 8)) (Seq.slice s 0 8)

#set-options "--initial_fuel 0 --max_fuel 0 --z3timeout 10"

val lemma_toField_1:
  s:Buffer.buffer U8.t{length s = 16} ->
  h:HyperStack.mem{live h s} ->
  n0:U64.t -> n1:U64.t -> n2:U64.t -> n3:U64.t ->
  Lemma (requires (let open FStar.UInt8 in
    U64.v n0 == v (get h s 0) + pow2 8 * v (get h s 1) + pow2 16 * v (get h s 2) + pow2 24 * v (get h s 3)
    /\ U64.v n1 == v (get h s 4) + pow2 8 * v (get h s 5) + pow2 16 * v (get h s 6) + pow2 24 * v (get h s 7)
    /\ U64.v n2 == v (get h s 8) + pow2 8 * v (get h s 9) + pow2 16 * v (get h s 10) + pow2 24 * v (get h s 11)
    /\ U64.v n3 == v (get h s 12) + pow2 8 * v (get h s 13) + pow2 16 * v (get h s 14) + pow2 24 * v (get h s 15)))
        (ensures  (v n0 + pow2 32 * v n1 + pow2 64 * v n2 + pow2 96 * v n3 = little_endian (as_seq h s)))
let lemma_toField_1 s h n0 n1 n2 n3 =
  let open FStar.Seq in
  let s' = as_seq h s in
  lemma_word_vals s h;
  let s04 = Seq.slice s' 0 4 in
  let s48 = Seq.slice s' 4 8 in
  let s812 = Seq.slice s' 8 12 in
  let s1216 = Seq.slice s' 12 16 in
  lemma_little_endian_of_u64 n0 s04;
  lemma_little_endian_of_u64 n1 s48;
  lemma_little_endian_of_u64 n2 s812;
  lemma_little_endian_of_u64 n3 s1216;
  lemma_seq_append_16_to_4 s';
  little_endian_append s04 s48;
  little_endian_append (Seq.append s04 s48) s812;
  little_endian_append (Seq.append (Seq.append s04 s48) s812) s1216
