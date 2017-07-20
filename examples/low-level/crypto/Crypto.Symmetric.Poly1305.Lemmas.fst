module Crypto.Symmetric.Poly1305.Lemmas

open FStar.Mul
open FStar.Ghost
open FStar.Seq
(** Machine integers *)
open FStar.UInt
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

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

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

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

private val mk_mask: nbits:FStar.UInt32.t{FStar.UInt32.v nbits < 64} ->
  Tot (z:U64.t{v z == pow2 (FStar.UInt32.v nbits) - 1})
let mk_mask nbits =
  Math.Lemmas.pow2_lt_compat 64 (FStar.UInt32.v nbits);
  U64.((1uL <<^ nbits) -^ 1uL)


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

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
  logand_mask (v (n0)) 26;
  logand_mask (v ((n1 <<^ 6ul))) 26;
  logand_mask (v ((n2 <<^ 12ul))) 26;
  logand_mask (v ((n3 <<^ 18ul))) 26;
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


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val lemma_toField_2_2: x:nat{x < pow2 32} -> Lemma
  (pow2 52 * ((x * pow2 12) % pow2 26) + pow2 78 * (x / pow2 14) = pow2 64 * x)
let lemma_toField_2_2 x =
  Math.Lemmas.pow2_plus 52 12;
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 x 26 12;
  cut ((x * pow2 12) % pow2 26 = pow2 12 * (x % (pow2 14)));
  Math.Lemmas.pow2_plus 64 14;
  Math.Lemmas.lemma_div_mod x (pow2 14);
  Math.Lemmas.distributivity_add_right (pow2 64) (x % pow2 14) (pow2 14 * (x / pow2 14))

val lemma_toField_2_3: x:nat{x < pow2 32} -> Lemma
  (pow2 78 * ((x * pow2 18) % pow2 26) + pow2 104 * (x / pow2 8) = pow2 96 * x)
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


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

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
  logand_mask #64 (v n0) 26;
  lemma_toField_2_0 n0 n1 n2 n3;
  let v0_26 = v (n0 >>^ 26ul) in
  let v1_6 = v ((n1 <<^ 6ul) &^ mask_26) in
  let v1_20 = v (n1 >>^ 20ul) in
  let v2_12 = v ((n2 <<^ 12ul) &^ mask_26) in
  let v2_14 = v (n2 >>^ 14ul) in
  let v3_18 = v ((n3 <<^ 18ul) &^ mask_26) in
  let v3_8 = v (n3 >>^ 8ul) in
  logor_disjoint v1_6 v0_26 6;
  UInt.logor_commutative v1_6 v0_26;
  logor_disjoint v2_12 v1_20 12;
  UInt.logor_commutative v2_12 v1_20;
  logor_disjoint v3_18 v2_14 18;
  UInt.logor_commutative v3_18 v2_14;
  Math.Lemmas.nat_times_nat_is_nat (v n1) (pow2 6);
  Math.Lemmas.nat_times_nat_is_nat (v n2) (pow2 12);
  Math.Lemmas.nat_times_nat_is_nat (v n3) (pow2 18);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v n1 * pow2 6) 26 64;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v n2 * pow2 12) 26 64;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v n3 * pow2 18) 26 64;
  logand_mask #64 (v n0) 26;
  logand_mask #64 (v (n1 <<^ 6ul)) 26;
  logand_mask #64 (v (n2 <<^ 12ul)) 26;
  logand_mask #64 (v (n3 <<^ 18ul)) 26;
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


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

private val add_disjoint: #z:pos -> a:UInt.uint_t z -> b:UInt.uint_t z -> n:nat -> m:nat{m < z} -> Lemma
  (requires (a % pow2 m = 0 /\ b < pow2 m /\ a < pow2 n /\ n >= m))
  (ensures  (a + b < pow2 n))
let add_disjoint #z a b n m =
  let c = a / pow2 m in
  Math.Lemmas.lemma_div_exact a (pow2 m);
  cut(a + b < c * pow2 m + pow2 m);
  Math.Lemmas.pow2_plus (n-m) m;
  cut(c < pow2 (n-m));
  Math.Lemmas.distributivity_add_right (pow2 m) c 1

#reset-options

(* n renamed into n', because n is shadowed by U64.n *)
val lemma_disjoint_bounded:
  b0:U64.t -> b1:U64.t -> l:nat -> m:pos{m >= l} -> n':nat{n' > m /\ n' <= 64} ->
  Lemma (requires (U64.(v b0 < pow2 m /\ v b1 % pow2 m = 0 /\ v b1 < pow2 n' /\ v b0 % pow2 l = 0)))
        (ensures  (U64.(v (b0 |^ b1) = v b0 + v b1 /\ v b0 + v b1 < pow2 n' /\ (v b0 + v b1) % pow2 l = 0)))
let lemma_disjoint_bounded b0 b1 l m n =
  let n' = n in (* n shadowed by FStar.UInt64.n *)
  let open FStar.UInt64 in
  let n = n' in
  logor_disjoint (v b1) (v b0) m;
  add_disjoint (v b1) (v b0) n m;
  UInt.logor_commutative (v b0) (v b1);
  lemma_mod_pow2 (v b1) m l;
  Math.Lemmas.lemma_mod_plus_distr_l (v b0) (v b1) (pow2 l);
  Math.Lemmas.lemma_mod_plus_distr_l (v b1) ((v b0) % pow2 l) (pow2 l)

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

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
  logand_mask #64 (v n0) 26;
  lemma_toField_2_0 n0 n1 n2 n3;
  let v0_26 = v (n0 >>^ 26ul) in
  let v1_6 = v ((n1 <<^ 6ul) &^ mask_26) in
  let v1_20 = v (n1 >>^ 20ul) in
  let v2_12 = v ((n2 <<^ 12ul) &^ mask_26) in
  let v2_14 = v (n2 >>^ 14ul) in
  let v3_18 = v ((n3 <<^ 18ul) &^ mask_26) in
  let v3_8 = v (n3 >>^ 8ul) in
  logor_disjoint v1_6 v0_26 6;
  UInt.logor_commutative v1_6 v0_26;
  logor_disjoint v2_12 v1_20 12;
  UInt.logor_commutative v2_12 v1_20;
  logor_disjoint v3_18 v2_14 18;
  UInt.logor_commutative v3_18 v2_14;
  lemma_disjoint_bounded (n0 >>^ 26ul) ((n1 <<^ 6ul) &^ mask_26) 0 6 26;
  lemma_disjoint_bounded (n1 >>^ 20ul) ((n2 <<^ 12ul) &^ mask_26) 0 12 26;
  lemma_disjoint_bounded (n2 >>^ 14ul) ((n3 <<^ 18ul) &^ mask_26) 0 18 26;
  lemma_div_pow2_lt (v n3) 32 8


#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 5"

(* The little_endian function but computed from the most significant bit, makes the
   enrolling of the function to concrete values easiers for math *)
let rec little_endian_from_top (s:Seq.seq U8.t) (len:nat{len <= Seq.length s}) : GTot nat
  = if len = 0 then 0
    else pow2 (8 * (len - 1)) * U8.v (Seq.index s (len-1)) + little_endian_from_top s (len-1)


#set-options "--z3rlimit 50 --initial_fuel 1 --max_fuel 1"

val lemma_little_endian_from_top_:
  s:Seq.seq U8.t{Seq.length s > 0} -> len:nat{len <= Seq.length s} ->
  Lemma (little_endian (Seq.slice s 0 len) = little_endian_from_top s len)
let rec lemma_little_endian_from_top_ s len =
  if len = 0 then ()
  else
    begin
    lemma_little_endian_from_top_ s (len-1);
    let s' = Seq.slice s 0 (len-1) in
    let s'' = Seq.slice s (len-1) len in
    Seq.lemma_eq_intro (Seq.slice s 0 len) (Seq.append s' s'');
    Seq.lemma_eq_intro s'' (Seq.create 1 (Seq.index s (len-1)));
    little_endian_append s' s'';
    little_endian_singleton (Seq.index s (len-1))
    end


#set-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_little_endian_from_top: s:Seq.seq U8.t{Seq.length s > 0} -> Lemma
  (little_endian s = little_endian_from_top s (Seq.length s))
let lemma_little_endian_from_top s =
  Seq.lemma_eq_intro s (Seq.slice s 0 (Seq.length s));
  lemma_little_endian_from_top_ s (Seq.length s)

#set-options "--z3rlimit 5 --initial_fuel 1 --max_fuel 1"

val lemma_little_endian_from_top_def: s:Seq.seq U8.t -> len:nat{Seq.length s >= len} ->
  Lemma ((len = 0 ==> little_endian_from_top s len = 0)
       /\ (len > 0 ==> little_endian_from_top s len =
                     pow2 (8*(len-1)) * U8.v (Seq.index s (len-1))
                     + little_endian_from_top s (len-1)))
let lemma_little_endian_from_top_def s len = ()


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

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


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

private let lemma_get_word #a (b:Buffer.buffer a) (h:HyperStack.mem{live h b}) (i:nat{i < Buffer.length b}) :
  Lemma (Seq.index (as_seq h b) i == get h b i)
  = ()

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 40"

private let lemma_word_vals (w:Buffer.buffer U8.t{Buffer.length w = 16}) (h:HyperStack.mem{live h w}) :
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

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val lemma_toField_1:
  s:Buffer.buffer U8.t{Buffer.length s = 16} ->
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


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val lemma_eval_5: h:HyperStack.mem -> a:Buffer.buffer U64.t{live h a /\ length a >= 5} ->
  Lemma (Crypto.Symmetric.Poly1305.Bigint.eval h a 5 =
    v (get h a 0) + pow2 26 * v (get h a 1) + pow2 52 * v (get h a 2) + pow2 78 * v (get h a 3)
    + pow2 104 * v (get h a 4))
let lemma_eval_5 h a =
  Crypto.Symmetric.Poly1305.Bigint.eval_def h a 5;
  Crypto.Symmetric.Poly1305.Bigint.eval_def h a 4;
  Crypto.Symmetric.Poly1305.Bigint.eval_def h a 3;
  Crypto.Symmetric.Poly1305.Bigint.eval_def h a 2;
  Crypto.Symmetric.Poly1305.Bigint.eval_def h a 1;
  Crypto.Symmetric.Poly1305.Bigint.eval_def h a 0;
  Crypto.Symmetric.Poly1305.Bigint.bitweight_def Crypto.Symmetric.Poly1305.Parameters.templ 4;
  Crypto.Symmetric.Poly1305.Bigint.bitweight_def Crypto.Symmetric.Poly1305.Parameters.templ 3;
  Crypto.Symmetric.Poly1305.Bigint.bitweight_def Crypto.Symmetric.Poly1305.Parameters.templ 2;
  Crypto.Symmetric.Poly1305.Bigint.bitweight_def Crypto.Symmetric.Poly1305.Parameters.templ 1;
  Crypto.Symmetric.Poly1305.Bigint.bitweight_def Crypto.Symmetric.Poly1305.Parameters.templ 0;
  assert_norm (pow2 0 = 1)

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"


val lemma_little_endian_16: h:HyperStack.mem -> a:Buffer.buffer U8.t{live h a /\ length a = 16} ->
  Lemma (let open FStar.UInt8 in
    little_endian (as_seq h a) =
            v (get h a 0) + pow2 8 * v (get h a 1) + pow2 16 * v (get h a 2) + pow2 24 * v (get h a 3)
  + pow2 32 * v (get h a 4) + pow2 40 * v (get h a 5) + pow2 48 * v (get h a 6) + pow2 56 * v (get h a 7)
  + pow2 64 * v (get h a 8) + pow2 72 * v (get h a 9) + pow2 80 * v (get h a 10) + pow2 88 * v (get h a 11)
  + pow2 96 * v (get h a 12) + pow2 104 * v (get h a 13) + pow2 112 * v (get h a 14) + pow2 120 * v (get h a 15) )
let lemma_little_endian_16 h a =
  let s = as_seq h a in
  lemma_little_endian_from_top s;
  lemma_little_endian_from_top_def s 16;
  lemma_little_endian_from_top_def s 15;
  lemma_little_endian_from_top_def s 14;
  lemma_little_endian_from_top_def s 13;
  lemma_little_endian_from_top_def s 12;
  lemma_little_endian_from_top_def s 11;
  lemma_little_endian_from_top_def s 10;
  lemma_little_endian_from_top_def s 9;
  lemma_little_endian_from_top_def s 8;
  lemma_little_endian_from_top_def s 7;
  lemma_little_endian_from_top_def s 6;
  lemma_little_endian_from_top_def s 5;
  lemma_little_endian_from_top_def s 4;
  lemma_little_endian_from_top_def s 3;
  lemma_little_endian_from_top_def s 2;
  lemma_little_endian_from_top_def s 1;
  lemma_little_endian_from_top_def s 0;
  assert_norm (pow2 0 = 1)


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"


let lemma_mul_mod (a:nat) (b:pos) : Lemma ((b * a) % b = 0) = Math.Lemmas.lemma_mod_plus 0 a b


val add_disjoint_bounded:
  b0:nat -> b1:nat -> m:nat -> n:nat{n > m} ->
  Lemma (requires ((b0 < pow2 m /\ b1 % pow2 m = 0 /\ b1 < pow2 n)))
        (ensures  (b0 + b1 < pow2 n))
let add_disjoint_bounded b0 b1 m n =
  Math.Lemmas.lemma_div_mod b1 (pow2 m);
  Math.Lemmas.lemma_mod_plus 0 b1 (pow2 m);
  let c = b1 / pow2 m in
  cut (c * pow2 m = b1);
  cut ( (b1 + b0) = ((c*pow2 m) + b0));
  lemma_div_pow2_lt b1 n m;
  Math.Lemmas.pow2_plus (n-m) m;
  cut ((c)*pow2 m + b0 < (pow2 (n-m)-1) * pow2 m + pow2 m)

val lemma_trunc1305_0: a:U64.t -> Lemma
  ((v a % pow2 8) + pow2 8 * ((v a / pow2 8) % pow2 8) + pow2 16 * ((v a / pow2 16) % pow2 8) + pow2 24 * ((v a / pow2 24) % pow2 8)
    = v a % pow2 32)
let lemma_trunc1305_0 a =
  assert_norm (pow2 0 = 1);
  (* lemma_mul_mod ((v a / pow2 8) % pow2 8) (pow2 8); *)
  (* Math.Lemmas.pow2_plus 8 8; *)
  (* Math.Lemmas.pow2_plus 16 8; *)
  (* add_disjoint_bounded (v a % pow2 8) (pow2 8 * ((v a / pow2 8) % pow2 8)) 8 16; *)
  (* lemma_mul_mod ((v a / pow2 16) % pow2 8) (pow2 8); *)
  (* add_disjoint_bounded ((v a % pow2 8) + pow2 8 * ((v a / pow2 8) % pow2 8)) *)
  (*                            (pow2 16 * ((v a / pow2 16) % pow2 8)) 16 24; *)
  (* lemma_mul_mod ((v a / pow2 24) % pow2 8) (pow2 8); *)
  (* add_disjoint_bounded ((v a % pow2 8) + pow2 8 * ((v a / pow2 8) % pow2 8) + pow2 16 * ((v a / pow2 16) % pow2 8)) *)
  (*                            (pow2 24 * ((v a / pow2 24) % pow2 8)) 24 32; *)
   let va32 = v a % pow2 32 in
   Math.Lemmas.pow2_modulo_modulo_lemma_1 (v a) 8 32;
   Math.Lemmas.pow2_modulo_modulo_lemma_1 (v a) 16 32;
   Math.Lemmas.pow2_modulo_modulo_lemma_1 (v a) 24 32;
   Math.Lemmas.lemma_div_mod (va32) (pow2 24);
   lemma_div_pow2_mod va32 32 24;
   cut (va32 = pow2 24 * ((va32 / pow2 24) % pow2 8) + (va32 % pow2 24));
   Math.Lemmas.lemma_div_mod (va32 % pow2 24) (pow2 16);
   Math.Lemmas.pow2_modulo_division_lemma_1 va32 16 24;
   Math.Lemmas.pow2_modulo_modulo_lemma_1 va32 16 24;
   cut (va32 % pow2 24 = pow2 16 * ((va32/pow2 16)%pow2 8) + (va32 % pow2 16));
   Math.Lemmas.lemma_div_mod (va32 % pow2 16) (pow2 8);
   Math.Lemmas.pow2_modulo_division_lemma_1 va32 8 16;
   Math.Lemmas.pow2_modulo_modulo_lemma_1 va32 8 16;
   cut (va32 % pow2 16 = pow2 8 * ((va32/pow2 8)%pow2 8) + (va32 % pow2 8));

  Math.Lemmas.pow2_modulo_division_lemma_1 (v a) 24 32;
  cut (((v a % pow2 32) / pow2 24) % pow2 8 = (v a / pow2 24) % pow2 8);
  Math.Lemmas.pow2_modulo_division_lemma_1 (v a) 16 32;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v a / pow2 16) 8 16;
  cut (((v a % pow2 32) / pow2 16) % pow2 8 = (v a / pow2 16) % pow2 8);
  Math.Lemmas.pow2_modulo_division_lemma_1 (v a) 8 32;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v a / pow2 8) 8 24;
  cut (((v a % pow2 32) / pow2 8) % pow2 8 = (v a / pow2 8) % pow2 8)


val lemma_trunc1305_1: a:U64.t -> Lemma
  (((v a * pow2 2) % pow2 8) + pow2 8 * ((v a / pow2 6) % pow2 8) + pow2 16 * ((v a / pow2 14) % pow2 8) + pow2 24 * ((v a / pow2 22) % pow2 8)
    = pow2 2 * (v a % pow2 30))
let lemma_trunc1305_1 a =
  let va32 = ((v a * pow2 2) % pow2 32) in
  Math.Lemmas.lemma_div_mod (va32) (pow2 24);
  lemma_div_pow2_mod va32 32 24;
  cut (va32 = pow2 24 * ((va32 / pow2 24) % pow2 8) + (va32 % pow2 24));
  Math.Lemmas.pow2_modulo_division_lemma_1 (v a * pow2 2) 24 32;
  cut (va32 / pow2 24 = ((v a * pow2 2) / pow2 24) % pow2 8);
  Math.Lemmas.pow2_multiplication_division_lemma_2 (v a) 24 2;
  cut ( (va32 / pow2 24) % pow2 8 = (v a / pow2 22) % pow2 8);

  Math.Lemmas.lemma_div_mod (va32 % pow2 24) (pow2 16);
  Math.Lemmas.pow2_modulo_division_lemma_1 va32 16 24;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 va32 16 24;
  cut (va32 % pow2 24 = pow2 16 * ((va32/pow2 16)%pow2 8) + (va32 % pow2 16));

  Math.Lemmas.pow2_modulo_division_lemma_1 (v a * pow2 2) 16 32;
  cut (va32 / pow2 16 = ((v a * pow2 2) / pow2 16) % pow2 16);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 ((v a * pow2 2) / pow2 16) 8 16;
  Math.Lemmas.pow2_multiplication_division_lemma_2 (v a) 16 2;
  cut ( (va32 / pow2 16) % pow2 8 = (v a / pow2 14) % pow2 8);

  Math.Lemmas.lemma_div_mod (va32 % pow2 16) (pow2 8);
  Math.Lemmas.pow2_modulo_division_lemma_1 va32 8 16;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 va32 8 16;
  cut (va32 % pow2 16 = pow2 8 * ((va32/pow2 8)%pow2 8) + (va32 % pow2 8));

  Math.Lemmas.pow2_modulo_division_lemma_1 (v a * pow2 2) 8 32;
  cut (va32 / pow2 8 = ((v a * pow2 2) / pow2 8) % pow2 24);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 ((v a * pow2 2) / pow2 8) 8 24;
  Math.Lemmas.pow2_multiplication_division_lemma_2 (v a) 8 2;
  cut ( (va32 / pow2 8) % pow2 8 = (v a / pow2 6) % pow2 8);

  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v a * pow2 2) 8 32;
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v a) 32 2


val lemma_trunc1305_2: a:U64.t -> Lemma
  (((v a * pow2 4) % pow2 8) + pow2 8 * ((v a / pow2 4) % pow2 8) + pow2 16 * ((v a / pow2 12) % pow2 8) + pow2 24 * ((v a / pow2 20) % pow2 8)
    = pow2 4 * (v a % pow2 28))
let lemma_trunc1305_2 a =
  let va32 = ((v a * pow2 4) % pow2 32) in
  Math.Lemmas.lemma_div_mod (va32) (pow2 24);
  lemma_div_pow2_mod va32 32 24;
  cut (va32 = pow2 24 * ((va32 / pow2 24) % pow2 8) + (va32 % pow2 24));
  Math.Lemmas.pow2_modulo_division_lemma_1 (v a * pow2 4) 24 32;
  cut (va32 / pow2 24 = ((v a * pow2 4) / pow2 24) % pow2 8);
  Math.Lemmas.pow2_multiplication_division_lemma_2 (v a) 24 4;
  cut ( (va32 / pow2 24) % pow2 8 = (v a / pow2 20) % pow2 8);

  Math.Lemmas.lemma_div_mod (va32 % pow2 24) (pow2 16);
  Math.Lemmas.pow2_modulo_division_lemma_1 va32 16 24;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 va32 16 24;
  cut (va32 % pow2 24 = pow2 16 * ((va32/pow2 16)%pow2 8) + (va32 % pow2 16));

  Math.Lemmas.pow2_modulo_division_lemma_1 (v a * pow2 4) 16 32;
  cut (va32 / pow2 16 = ((v a * pow2 4) / pow2 16) % pow2 16);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 ((v a * pow2 4) / pow2 16) 8 16;
  Math.Lemmas.pow2_multiplication_division_lemma_2 (v a) 16 4;
  cut ( (va32 / pow2 16) % pow2 8 = (v a / pow2 12) % pow2 8);

  Math.Lemmas.lemma_div_mod (va32 % pow2 16) (pow2 8);
  Math.Lemmas.pow2_modulo_division_lemma_1 va32 8 16;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 va32 8 16;
  cut (va32 % pow2 16 = pow2 8 * ((va32/pow2 8)%pow2 8) + (va32 % pow2 8));

  Math.Lemmas.pow2_modulo_division_lemma_1 (v a * pow2 4) 8 32;
  cut (va32 / pow2 8 = ((v a * pow2 4) / pow2 8) % pow2 24);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 ((v a * pow2 4) / pow2 8) 8 24;
  Math.Lemmas.pow2_multiplication_division_lemma_2 (v a) 8 4;
  cut ( (va32 / pow2 8) % pow2 8 = (v a / pow2 4) % pow2 8);

  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v a * pow2 4) 8 32;
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v a) 32 4

val lemma_trunc1305_3: a:U64.t -> Lemma
  (((v a * pow2 6) % pow2 8) + pow2 8 * ((v a / pow2 2) % pow2 8) + pow2 16 * ((v a / pow2 10) % pow2 8) + pow2 24 * ((v a / pow2 18) % pow2 8)
    = pow2 6 * (v a % pow2 26))
let lemma_trunc1305_3 a =
  let va32 = ((v a * pow2 6) % pow2 32) in
  Math.Lemmas.lemma_div_mod (va32) (pow2 24);
  lemma_div_pow2_mod va32 32 24;
  cut (va32 = pow2 24 * ((va32 / pow2 24) % pow2 8) + (va32 % pow2 24));
  Math.Lemmas.pow2_modulo_division_lemma_1 (v a * pow2 6) 24 32;
  cut (va32 / pow2 24 = ((v a * pow2 6) / pow2 24) % pow2 8);
  Math.Lemmas.pow2_multiplication_division_lemma_2 (v a) 24 6;
  cut ( (va32 / pow2 24) % pow2 8 = (v a / pow2 18) % pow2 8);

  Math.Lemmas.lemma_div_mod (va32 % pow2 24) (pow2 16);
  Math.Lemmas.pow2_modulo_division_lemma_1 va32 16 24;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 va32 16 24;
  cut (va32 % pow2 24 = pow2 16 * ((va32/pow2 16)%pow2 8) + (va32 % pow2 16));

  Math.Lemmas.pow2_modulo_division_lemma_1 (v a * pow2 6) 16 32;
  cut (va32 / pow2 16 = ((v a * pow2 6) / pow2 16) % pow2 16);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 ((v a * pow2 6) / pow2 16) 8 16;
  Math.Lemmas.pow2_multiplication_division_lemma_2 (v a) 16 6;
  cut ( (va32 / pow2 16) % pow2 8 = (v a / pow2 10) % pow2 8);

  Math.Lemmas.lemma_div_mod (va32 % pow2 16) (pow2 8);
  Math.Lemmas.pow2_modulo_division_lemma_1 va32 8 16;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 va32 8 16;
  cut (va32 % pow2 16 = pow2 8 * ((va32/pow2 8)%pow2 8) + (va32 % pow2 8));

  Math.Lemmas.pow2_modulo_division_lemma_1 (v a * pow2 6) 8 32;
  cut (va32 / pow2 8 = ((v a * pow2 6) / pow2 8) % pow2 24);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 ((v a * pow2 6) / pow2 8) 8 24;
  Math.Lemmas.pow2_multiplication_division_lemma_2 (v a) 8 6;
  cut ( (va32 / pow2 8) % pow2 8 = (v a / pow2 2) % pow2 8);

  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v a * pow2 6) 8 32;
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v a) 32 6

val lemma_trunc1305_4: a:U64.t -> Lemma
  ((v a % pow2 8) + pow2 8 * ((v a / pow2 8) % pow2 8) + pow2 16 * ((v a / pow2 16) % pow2 8)
    = v a % pow2 24)
let lemma_trunc1305_4 a =
   let va32 = v a % pow2 32 in
   Math.Lemmas.pow2_modulo_modulo_lemma_1 (v a) 8 32;
   Math.Lemmas.pow2_modulo_modulo_lemma_1 (v a) 16 32;
   Math.Lemmas.pow2_modulo_modulo_lemma_1 (v a) 24 32;
   Math.Lemmas.lemma_div_mod (va32) (pow2 24);
   lemma_div_pow2_mod va32 32 24;
   cut (va32 = pow2 24 * ((va32 / pow2 24) % pow2 8) + (va32 % pow2 24));
   Math.Lemmas.lemma_div_mod (va32 % pow2 24) (pow2 16);
   Math.Lemmas.pow2_modulo_division_lemma_1 va32 16 24;
   Math.Lemmas.pow2_modulo_modulo_lemma_1 va32 16 24;
   cut (va32 % pow2 24 = pow2 16 * ((va32/pow2 16)%pow2 8) + (va32 % pow2 16));
   Math.Lemmas.lemma_div_mod (va32 % pow2 16) (pow2 8);
   Math.Lemmas.pow2_modulo_division_lemma_1 va32 8 16;
   Math.Lemmas.pow2_modulo_modulo_lemma_1 va32 8 16;
   cut (va32 % pow2 16 = pow2 8 * ((va32/pow2 8)%pow2 8) + (va32 % pow2 8));

  Math.Lemmas.pow2_modulo_division_lemma_1 (v a) 24 32;
  cut (((v a % pow2 32) / pow2 24) % pow2 8 = (v a / pow2 24) % pow2 8);
  Math.Lemmas.pow2_modulo_division_lemma_1 (v a) 16 32;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v a / pow2 16) 8 16;
  cut (((v a % pow2 32) / pow2 16) % pow2 8 = (v a / pow2 16) % pow2 8);
  Math.Lemmas.pow2_modulo_division_lemma_1 (v a) 8 32;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v a / pow2 8) 8 24;
  cut (((v a % pow2 32) / pow2 8) % pow2 8 = (v a / pow2 8) % pow2 8)


val lemma_norm_5:
  h:HyperStack.mem ->
  b:Buffer.buffer U64.t{length b >= 5 /\ Crypto.Symmetric.Poly1305.Bigint.norm h b} ->
  Lemma (requires (True))
        (ensures  (v (get h b 0) < pow2 26 /\ v (get h b 1) < pow2 26
          /\ v (get h b 2) < pow2 26 /\ v (get h b 3) < pow2 26 /\ v (get h b 4) < pow2 26))
let lemma_norm_5 h b = ()


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val lemma_mod_sum_mul: x:nat -> y:nat -> l:nat -> m:nat -> Lemma
  (requires (x % pow2 l = 0 /\ y < pow2 l /\ m >= l))
  (ensures  ( (x + y) % pow2 m = x % pow2 m + y))
let lemma_mod_sum_mul x y l m =
  Math.Lemmas.lemma_mod_plus_distr_l x y (pow2 m);
  cut ( (x + y) % pow2 m = (x % pow2 m + y) % pow2 m);
  Math.Lemmas.lemma_div_mod x (pow2 l);
  let c = x / pow2 l in
  cut (c * pow2 l = x);
  cut ( (x + y) % pow2 m = (((c*pow2 l)%pow2 m) + y) % pow2 m);
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 c m l;
  cut ( (x + y) % pow2 m = (((c%pow2 (m-l))*pow2 l) + y) % pow2 m);
  cut ( c % pow2 (m - l) < pow2 (m - l)); cut ((c%pow2 (m-l))*pow2 l + y < (pow2 (m-l)-1) * pow2 l + pow2 l);
    Math.Lemmas.pow2_plus (m-l) l; Math.Lemmas.modulo_lemma (((c%pow2 (m-l))*pow2 l) + y) (pow2 m)


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

let lemma_b3 (a0:U64.t{v a0 < pow2 26}) (a1:U64.t{v a1 < pow2 26}) : Lemma
  (pow2 24 * (U8.v (uint64_to_uint8 ((a0 >>^ 24ul) |^ (a1 <<^ 2ul)))) = pow2 24 * ((v a0 / pow2 24) % pow2 8) + pow2 24 * ((v a1*pow2 2)%pow2 8))
  = cut (v (a0 >>^ 24ul) = v a0 / pow2 24);
    Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v a1) 64 2;
    Math.Lemmas.pow2_lt_compat 62 26; Math.Lemmas.modulo_lemma (v a1) (pow2 62);
    Math.Lemmas.lemma_mod_plus 0 (v a1) (pow2 2);
    lemma_div_pow2_lt (v a0) 26 24;
    cut (v (a1 <<^ 2ul) % pow2 2 = 0);
    cut (v (a0 >>^ 24ul) < pow2 2);
    assert_norm(pow2 0 = 1);
    Math.Lemmas.pow2_plus 26 2;
    lemma_disjoint_bounded (a0 >>^ 24ul) (a1 <<^ 2ul) 0 2 28;
    let r = U8.v (uint64_to_uint8 ((a0 >>^ 24ul) |^ (a1 <<^ 2ul))) in
    cut (r = ((v a0 / pow2 24) + (v a1 * pow2 2)) % pow2 8);
    lemma_mod_sum_mul (v a1 * pow2 2) (v a0 / pow2 24) 2 8

#reset-options "--z3rlimit 1000 --max_fuel 10"

let lemma_b6 (a1:U64.t{v a1 < pow2 26}) (a2:U64.t{v a2 < pow2 26}) : Lemma
  (pow2 48 * (U8.v (uint64_to_uint8 ((a1 >>^ 22ul) |^ (a2 <<^ 4ul)))) = pow2 48 * ((v a1 / pow2 22) % pow2 8) + pow2 48 * ((v a2*pow2 4)%pow2 8))
  = cut (v (a1 >>^ 22ul) = v a1 / pow2 22);
    Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v a2) 64 4;
    Math.Lemmas.pow2_lt_compat 60 26; Math.Lemmas.modulo_lemma (v a2) (pow2 60);
    Math.Lemmas.lemma_mod_plus 0 (v a2) (pow2 4);
    lemma_div_pow2_lt (v a1) 26 22;
    cut (v (a2 <<^ 4ul) % pow2 4 = 0);
    cut (v (a1 >>^ 22ul) < pow2 4);
    assert_norm(pow2 0 = 1);
    Math.Lemmas.pow2_plus 26 4;
    lemma_disjoint_bounded (a1 >>^ 22ul) (a2 <<^ 4ul) 0 4 30;
    let r = U8.v (uint64_to_uint8 ((a1 >>^ 22ul) |^ (a2 <<^ 4ul))) in
    cut (r = ((v a1 / pow2 22) + (v a2 * pow2 4)) % pow2 8);
    lemma_mod_sum_mul (v a2 * pow2 4) (v a1 / pow2 22) 4 8


let lemma_b9 (a2:U64.t{v a2 < pow2 26}) (a3:U64.t{v a3 < pow2 26}) : Lemma
  (pow2 72 * (U8.v (uint64_to_uint8 ((a2 >>^ 20ul) |^ (a3 <<^ 6ul)))) = pow2 72 * ((v a2 / pow2 20) % pow2 8) + pow2 72 * ((v a3*pow2 6)%pow2 8))
  = cut (v (a2 >>^ 20ul) = v a2 / pow2 20);
    Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v a3) 64 6;
    Math.Lemmas.pow2_lt_compat 58 26; Math.Lemmas.modulo_lemma (v a3) (pow2 58);
    Math.Lemmas.lemma_mod_plus 0 (v a3) (pow2 6);
    lemma_div_pow2_lt (v a2) 26 20;
    cut (v (a3 <<^ 6ul) % pow2 6 = 0);
    cut (v (a2 >>^ 20ul) < pow2 6);
    assert_norm(pow2 0 = 1);
    Math.Lemmas.pow2_plus 26 6;
    lemma_disjoint_bounded (a2 >>^ 20ul) (a3 <<^ 6ul) 0 6 32;
    let r = U8.v (uint64_to_uint8 ((a2 >>^ 20ul) |^ (a3 <<^ 6ul))) in
    cut (r = ((v a2 / pow2 20) + (v a3 * pow2 6)) % pow2 8);
    lemma_mod_sum_mul (v a3 * pow2 6) (v a2 / pow2 20) 6 8



let lemma_distr_4 a b c d e : Lemma (a * (b+c+d+e) = a * b + a * c + a * d + a * e) = ()
let lemma_distr_3 a b c d : Lemma (a * (b+c+d) = a * b + a * c + a * d) = ()

let lemma_distr_4_1 b c d e : Lemma (pow2 24 * (b + pow2 8 * c + pow2 16 * d + pow2 24 * e)
  = pow2 24 * b + pow2 32 * c + pow2 40 * d + pow2 48 * e) =
    lemma_distr_4 (pow2 24) b (pow2 8 * c) (pow2 16 * d) (pow2 24 * d);
    Math.Lemmas.pow2_plus 24 8; Math.Lemmas.pow2_plus 24 16; Math.Lemmas.pow2_plus 24 24
let lemma_distr_4_2 b c d e : Lemma (pow2 48 * (b + pow2 8 * c + pow2 16 * d + pow2 24 * e)
  = pow2 48 * b + pow2 56 * c + pow2 64 * d + pow2 72 * e) =
    lemma_distr_4 (pow2 48) b (pow2 8 * c) (pow2 16 * d) (pow2 24 * d);
    Math.Lemmas.pow2_plus 48 8; Math.Lemmas.pow2_plus 48 16; Math.Lemmas.pow2_plus 48 24
let lemma_distr_4_3 b c d e : Lemma (pow2 72 * (b + pow2 8 * c + pow2 16 * d + pow2 24 * e)
  = pow2 72 * b + pow2 80 * c + pow2 88 * d + pow2 96 * e) =
    lemma_distr_4 (pow2 72) b (pow2 8 * c) (pow2 16 * d) (pow2 24 * d);
    Math.Lemmas.pow2_plus 72 8; Math.Lemmas.pow2_plus 72 16; Math.Lemmas.pow2_plus 72 24
let lemma_distr_4_4 b c d : Lemma (pow2 104 * (b + pow2 8 * c + pow2 16 * d)
  = pow2 104 * b + pow2 112 * c + pow2 120 * d) =
    lemma_distr_3 (pow2 104) b (pow2 8 * c) (pow2 16 * d);
    Math.Lemmas.pow2_plus 104 8; Math.Lemmas.pow2_plus 104 16

let lemma_b03a0 (a0:U64.t{v a0 < pow2 26}) (a1:UInt64.t{v a1 < pow2 26}) b0 b1 b2 b3 : Lemma
  (requires (let open FStar.UInt8 in
    v b0 = (U64.v a0) % pow2 8
    /\ v b1 = (U64.v a0 / pow2 8) % pow2 8
    /\ v b2 = (U64.v a0 / pow2 16) % pow2 8
    /\ pow2 24 * v b3 = pow2 24 * ((U64.v a0/pow2 24) % pow2 8) + pow2 24 * ((U64.v a1*pow2 2)%pow2 8)))
  (ensures (let open FStar.UInt8 in
    v b0 + pow2 8 * v b1 + pow2 16 * v b2 + pow2 24 * v b3 = (U64.v a0) % pow2 32 + pow2 24 * ((U64.v a1*pow2 2)%pow2 8)))
  = lemma_trunc1305_0 a0


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

let lemma_b46a1 (a1:U64.t{v a1 < pow2 26}) (a2:UInt64.t{v a2 < pow2 26}) v3 b4 b5 b6 : Lemma
  (requires (let open FStar.UInt8 in
    v3 = pow2 24 * ((U64.v a1*pow2 2)%pow2 8)
    /\ v b4 = (U64.v a1 / pow2 6) % pow2 8
    /\ v b5 = (U64.v a1 / pow2 14) % pow2 8
    /\ pow2 48 * v b6 = pow2 48 * ((U64.v a1 / pow2 22) % pow2 8) + pow2 48 * ((U64.v a2*pow2 4)%pow2 8)))
  (ensures (let open FStar.UInt8 in
    v3 + pow2 32 * v b4 + pow2 40 * v b5 + pow2 48 * v b6 = pow2 26 * (U64.v a1 % pow2 30)
      + pow2 48 * ((U64.v a2*pow2 4)%pow2 8)))
  = lemma_trunc1305_1 a1; Math.Lemmas.pow2_plus 24 2;
    Math.Lemmas.distributivity_add_right (pow2 24) (pow2 24 * ((U64.v a1 / pow2 22) % pow2 8)) (pow2 24 * ((U64.v a2*pow2 4)%pow2 8));
    Math.Lemmas.pow2_plus 24 24;
    cut (pow2 2 * (v a1 % pow2 30) = ((U64.v a1*pow2 2)%pow2 8) + pow2 8 * U8.v b4 + pow2 16 * U8.v b5 + pow2 24 * ((U64.v a1 / pow2 22) % pow2 8));
    lemma_distr_4_1 ((U64.v a1*pow2 2)%pow2 8) (U8.v b4) (U8.v b5) ((U64.v a1 / pow2 22) % pow2 8);
    cut (pow2 24 * (pow2 2 * (v a1 % pow2 30)) = v3 + pow2 32 * U8.v b4 + pow2 40 * U8.v b5
      + pow2 48 * ((U64.v a1 / pow2 22) % pow2 8));
    Math.Lemmas.paren_mul_right (pow2 24) (pow2 2) (v a1 % pow2 30)


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

let lemma_b79a2 (a2:U64.t{v a2 < pow2 26}) (a3:UInt64.t{v a3 < pow2 26}) v6 b7 b8 b9 : Lemma
  (requires (let open FStar.UInt8 in
    v6 = pow2 48 * ((U64.v a2*pow2 4)%pow2 8)
    /\ v b7 = (U64.v a2 / pow2 4) % pow2 8
    /\ v b8 = (U64.v a2 / pow2 12) % pow2 8
    /\ pow2 72 * v b9 = pow2 72 * ((U64.v a2 / pow2 20) % pow2 8) + pow2 72 * ((U64.v a3*pow2 6)%pow2 8)))
  (ensures (let open FStar.UInt8 in
    v6 + pow2 56 * v b7 + pow2 64 * v b8 + pow2 72 * v b9 = pow2 52 * (U64.v a2 % pow2 28)
      + pow2 72 * ((U64.v a3*pow2 6)%pow2 8)))
  = lemma_trunc1305_2 a2; Math.Lemmas.pow2_plus 48 4;
    Math.Lemmas.distributivity_add_right (pow2 48) (pow2 48 * ((U64.v a2 / pow2 20) % pow2 8)) (pow2 24 * ((U64.v a3*pow2 6)%pow2 8));
    Math.Lemmas.pow2_plus 48 24;
    cut (pow2 4 * (v a2 % pow2 28) = ((U64.v a2*pow2 4)%pow2 8) + pow2 8 * U8.v b7 + pow2 16 * U8.v b8 + pow2 24 * ((U64.v a2 / pow2 20) % pow2 8));
    lemma_distr_4_2 ((U64.v a2*pow2 4)%pow2 8) (U8.v b7) (U8.v b8) ((U64.v a2 / pow2 20) % pow2 8);
    cut (pow2 48 * (pow2 4 * (v a2 % pow2 28)) = v6 + pow2 56 * U8.v b7 + pow2 64 * U8.v b8
      + pow2 72 * ((U64.v a2 / pow2 20) % pow2 8));
    Math.Lemmas.paren_mul_right (pow2 48) (pow2 4) (v a2 % pow2 28)


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

let lemma_b1012a3 (a3:U64.t{v a3 < pow2 26}) v9 b10 b11 b12 : Lemma
  (requires (let open FStar.UInt8 in
    v9 = pow2 72 * ((U64.v a3*pow2 6)%pow2 8)
    /\ v b10 = (U64.v a3 / pow2 2) % pow2 8
    /\ v b11 = (U64.v a3 / pow2 10) % pow2 8
    /\ v b12 = ((U64.v a3 / pow2 18) % pow2 8) ))
  (ensures (let open FStar.UInt8 in
    v9 + pow2 80 * v b10 + pow2 88 * v b11 + pow2 96 * v b12 = pow2 78 * (U64.v a3 % pow2 26)))
  = lemma_trunc1305_3 a3; Math.Lemmas.pow2_plus 72 6;
    cut (pow2 6 * (v a3 % pow2 26) = ((U64.v a3*pow2 6)%pow2 8) + pow2 8 * U8.v b10 + pow2 16 * U8.v b11 + pow2 24 * U8.v b12);
    lemma_distr_4_3 ((U64.v a3*pow2 6)%pow2 8) (U8.v b10) (U8.v b11) (U8.v b12);
    cut (pow2 72 * (pow2 6 * (v a3 % pow2 26)) = v9 + pow2 80 * U8.v b10 + pow2 88 * U8.v b11
      + pow2 96 * U8.v b12);
    Math.Lemmas.paren_mul_right (pow2 72) (pow2 6) (v a3 % pow2 26)


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

let lemma_b1315a4 (a4:U64.t{v a4 < pow2 26}) b13 b14 b15 : Lemma
  (requires (let open FStar.UInt8 in
    v b13 = ((U64.v a4)%pow2 8)
    /\ v b14 = (U64.v a4 / pow2 8) % pow2 8
    /\ v b15 = (U64.v a4 / pow2 16) % pow2 8))
  (ensures (let open FStar.UInt8 in
    pow2 104 * v b13 + pow2 112 * v b14 + pow2 120 * v b15 = pow2 104 * (U64.v a4 % pow2 24)))
  = lemma_trunc1305_4 a4;
    lemma_distr_4_4 (U8.v b13) (U8.v b14) (U8.v b15)

let u26 = x:U64.t{v x < pow2 26}

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val lemma_trunc1305_:
  a0:u26 -> a1:u26 -> a2:u26 -> a3:u26 -> a4:u26 ->
  b0:U8.t -> b1:U8.t -> b2:U8.t -> b3:U8.t -> b4:U8.t -> b5:U8.t -> b6:U8.t -> b7:U8.t ->
  b8:U8.t -> b9:U8.t -> b10:U8.t -> b11:U8.t -> b12:U8.t -> b13:U8.t -> b14:U8.t -> b15:U8.t ->
  Lemma (requires (let open FStar.UInt8 in
    v b0 = (U64.v a0) % pow2 8
    /\ v b1 = (U64.v a0 / pow2 8) % pow2 8
    /\ v b2 = (U64.v a0 / pow2 16) % pow2 8
    /\ pow2 24 * v b3 = pow2 24 * ((U64.v a0/pow2 24) % pow2 8) + pow2 24 * ((U64.v a1*pow2 2)%pow2 8)
    /\ v b4 = (U64.v a1 / pow2 6) % pow2 8
    /\ v b5 = (U64.v a1 / pow2 14) % pow2 8
    /\ pow2 48 * v b6 = pow2 48 * ((U64.v a1 / pow2 22) % pow2 8) + pow2 48 * ((U64.v a2*pow2 4)%pow2 8)
    /\ v b7 = (U64.v a2 / pow2 4) % pow2 8
    /\ v b8 = (U64.v a2 / pow2 12) % pow2 8
    /\ pow2 72 * v b9 = pow2 72 * ((U64.v a2 / pow2 20) % pow2 8) + pow2 72 * ((U64.v a3*pow2 6)%pow2 8)
    /\ v b10 = (U64.v a3 / pow2 2) % pow2 8
    /\ v b11 = (U64.v a3 / pow2 10) % pow2 8
    /\ v b12 = ((U64.v a3 / pow2 18) % pow2 8)
    /\ v b13 = ((U64.v a4)%pow2 8)
    /\ v b14 = (U64.v a4 / pow2 8) % pow2 8
    /\ v b15 = (U64.v a4 / pow2 16) % pow2 8 ))
        (ensures  (U8.(v (b0) + pow2 8 * v (b1) + pow2 16 * v (b2) + pow2 24 * v (b3)
  + pow2 32 * v (b4) + pow2 40 * v (b5) + pow2 48 * v (b6) + pow2 56 * v (b7)
  + pow2 64 * v (b8) + pow2 72 * v (b9) + pow2 80 * v (b10) + pow2 88 * v (b11)
  + pow2 96 * v (b12) + pow2 104 * v (b13) + pow2 112 * v (b14) + pow2 120 * v (b15))
            = v a0 + pow2 26 * v a1 + pow2 52 * v a2 + pow2 78 * v a3 + pow2 104 * (v a4 % pow2 24)))

let lemma_sub a b c : Lemma (requires (a + b = c)) (ensures (a = a + b - b /\ a = c - b)) = ()
let lemma_paren a b c d : Lemma (a + (b + c + d) = a + b + c + d) = ()
let lemma_sum_ a b c d e f g h : Lemma ((a-b)+((b+c)-d)+((d+e)-f)+(f+g)+h=a+c+e+g+h) = ()
let lemma_sum' b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Lemma
  (b0+b1+b2+b3+b4+b5+b6+b7+b8+b9+b10+b11+b12+b13+b14+b15 = (b0+b1+b2+b3)+(b4+b5+b6)+(b7+b8+b9)+(b10+b11+b12)+(b13+b14+b15)) = ()

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

let lemma_trunc1305_ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 =
  lemma_b3 a0 a1;
  lemma_b6 a1 a2;
  lemma_b9 a2 a3;
  let open FStar.UInt8 in
  lemma_distr_4_1 ((U64.v a1*pow2 2)%pow2 8) (v b4) (v b5) ((U64.v a1 / pow2 22) % pow2 8);
  lemma_distr_4_2 ((U64.v a2*pow2 4)%pow2 8) (v b7) (v b8) ((U64.v a2 / pow2 20) % pow2 8);
  lemma_distr_4_3 ((U64.v a3*pow2 6)%pow2 8) (v b10) (v b11) (v b12);
  let v3 = pow2 24 * ((U64.v a1*pow2 2)%pow2 8) in
  let v6 = pow2 48 * ((U64.v a2*pow2 4)%pow2 8) in
  let v9 = pow2 72 * ((U64.v a3*pow2 6)%pow2 8) in
  let b03 = (v b0 + pow2 8 * v b1 + pow2 16 * v b2 + pow2 24 * v b3) in
  let b46 = pow2 32 * v (b4) + pow2 40 * v (b5) + pow2 48 * v (b6) in
  let b79 = pow2 56 * v (b7) + pow2 64 * v (b8) + pow2 72 * v (b9) in
  let b1012 = pow2 80 * v (b10) + pow2 88 * v (b11) + pow2 96 * v (b12) in
  let b1315 = pow2 104 * v (b13) + pow2 112 * v (b14) + pow2 120 * v (b15) in
  lemma_b03a0 a0 a1 b0 b1 b2 b3;
  lemma_b46a1 a1 a2 (v3) b4 b5 b6;
  lemma_paren v3 (pow2 32 * v (b4)) (pow2 40 * v (b5)) (pow2 48 * v (b6));
  cut ( pow2 26 * (U64.v a1 % pow2 30) + v6 = v3 + b46);
  lemma_b79a2 a2 a3 (v6) b7 b8 b9;
  lemma_paren v6 (pow2 56 * v (b7)) (pow2 64 * v (b8)) (pow2 72 * v (b9));
  cut ( pow2 52 * (U64.v a2 % pow2 28) + v9 = v6 + b79);
  lemma_b1012a3 a3 (v9) b10 b11 b12;
  lemma_paren v9 (pow2 80 * v (b10)) (pow2 88 * v (b11)) (pow2 96 * v (b12));
  cut ( pow2 78 * (U64.v a3 % pow2 26) = v9 + b1012);
  lemma_b1315a4 a4 b13 b14 b15;
  cut ( pow2 104 * (U64.v a4 % pow2 24) = b1315);
  lemma_sub ((U64.v a0) % pow2 32) v3 b03;
  let open FStar.UInt64 in
  cut ((v a0 % pow2 32) = b03 - v3);
  lemma_sub (pow2 26 * ((U64.v a1) % pow2 30)) v6 (v3 + b46);
  lemma_sub (pow2 52 * ((U64.v a2) % pow2 28)) v9 (v6 + b79);
  cut (pow2 26 * (v a1 % pow2 30) = (v3 + b46) - v6);
  cut (pow2 52 * (v a2 % pow2 28) = (v6 + b79) - v9);
  cut ((v a0 % pow2 32)
            + pow2 26 * (v a1 % pow2 30)
            + pow2 52 * (v a2 % pow2 28)
            + pow2 78 * (v a3 % pow2 26)
            + pow2 104 * (v a4 % pow2 24) = (b03 - v3) + ((v3 + b46) - v6) + ((v6 + b79) - v9)
              + (v9 + b1012) + b1315);
   lemma_sum_ b03 v3 b46 v6 b79 v9 b1012 b1315;
   let open FStar.UInt8 in
   lemma_sum' (v b0) (v b1) (v b2) (v b3) (v b4) (v b5) (v b6) (v b7) (v b8) (v b9) (v b10) (v b11) (v b12) (v b13) (v b14) (v b15);
   let open FStar.UInt64 in
   Math.Lemmas.pow2_lt_compat 32 26; Math.Lemmas.pow2_lt_compat 30 26;
   Math.Lemmas.pow2_lt_compat 28 26; Math.Lemmas.modulo_lemma (v a0) (pow2 32);
   Math.Lemmas.modulo_lemma (v a1) (pow2 30); Math.Lemmas.modulo_lemma (v a2) (pow2 28);
   Math.Lemmas.modulo_lemma (v a3) (pow2 26)


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

let lemma_mult_le_left (a:nat) (b:nat) (c:nat) : Lemma (requires (b <= c)) (ensures (a * b <= a * c)) = ()

val lemma_eval_mod: a0:u26 -> a1:u26 -> a2:u26 -> a3:u26 -> a4:u26 -> Lemma
  ((v a0 + pow2 26 * v a1 + pow2 52 * v a2 + pow2 78 * v a3 + pow2 104 * v a4) % pow2 128
    = v a0 + pow2 26 * v a1 + pow2 52 * v a2 + pow2 78 * v a3 + (pow2 104 * (v a4 % pow2 24)))
let lemma_eval_mod a0 a1 a2 a3 a4 =
  Math.Lemmas.lemma_mod_plus_distr_l (pow2 104 * v a4) (v a0 + pow2 26 * v a1 + pow2 52 * v a2 + pow2 78 * v a3) (pow2 128);
  let r' = v a0 + pow2 26 * v a1 + pow2 52 * v a2 + pow2 78 * v a3 in
  let r = (v a0 + pow2 26 * v a1 + pow2 52 * v a2 + pow2 78 * v a3 + pow2 104 * v a4) % pow2 128 in
  let r'' = (v a0 + pow2 26 * v a1 + pow2 52 * v a2 + pow2 78 * v a3 + pow2 104 * (v a4 % pow2 24)) in
  cut (r = (((pow2 104 * v a4)%pow2 128) + r') % pow2 128);
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v a4) 128 104;
  cut ((pow2 104 * v a4) % pow2 128 = pow2 104 * (v a4 % pow2 24));
  cut (r = r'' % pow2 128);
  lemma_mult_le_left (pow2 26) (v a1) (pow2 26 - 1);
  lemma_mult_le_left (pow2 52) (v a2) (pow2 26 - 1);
  lemma_mult_le_left (pow2 78) (v a3) (pow2 26 - 1);
  lemma_mult_le_left (pow2 104) (v a4 % pow2 24) (pow2 24 - 1);
  assert_norm ((pow2 26 - 1) + pow2 26 * (pow2 26 - 1) + pow2 52 * (pow2 26 - 1) + pow2 78 * (pow2 26 - 1) + (pow2 104 * ((pow2 24 - 1))) < pow2 128);
  Math.Lemmas.modulo_lemma ( v a0 + pow2 26 * v a1 + pow2 52 * v a2 + pow2 78 * v a3 + (pow2 104 * (v a4 % pow2 24))) (pow2 128)


val lemma_trunc1305: hb:HyperStack.mem ->
  b:Buffer.buffer U8.t{live hb b /\ length b = 16} ->
  ha:HyperStack.mem ->
  a:Crypto.Symmetric.Poly1305.Bigint.bigint{Crypto.Symmetric.Poly1305.Bigint.norm ha a} ->
  Lemma (requires (
    let a0 = get ha a 0 in let a1 = get ha a 1 in let a2 = get ha a 2 in let a3 = get ha a 3 in
    let a4 = get ha a 4 in
    let b0 = get hb b 0 in let b1 = get hb b 1 in let b2 = get hb b 2 in let b3 = get hb b 3 in
    let b4 = get hb b 4 in let b5 = get hb b 5 in let b6 = get hb b 6 in let b7 = get hb b 7 in
    let b8 = get hb b 8 in let b9 = get hb b 9 in let b10 = get hb b 10 in let b11 = get hb b 11 in
    let b12 = get hb b 12 in let b13 = get hb b 13 in let b14 = get hb b 14 in let b15 = get hb b 15 in
    ( b0 == uint64_to_uint8 a0
    /\ b1 == uint64_to_uint8 (a0 >>^ 8ul)
    /\ b2 == uint64_to_uint8 (a0 >>^ 16ul)
    /\ b3 == uint64_to_uint8 ((a0 >>^ 24ul) |^ (a1 <<^ 2ul))
    /\ b4 == uint64_to_uint8 (a1 >>^ 6ul)
    /\ b5 == uint64_to_uint8 (a1 >>^ 14ul)
    /\ b6 == uint64_to_uint8 ((a1 >>^ 22ul) |^ (a2 <<^ 4ul))
    /\ b7 == uint64_to_uint8 (a2 >>^ 4ul)
    /\ b8 == uint64_to_uint8 (a2 >>^ 12ul)
    /\ b9 == uint64_to_uint8 ((a2 >>^ 20ul) |^ (a3 <<^ 6ul))
    /\ b10 == uint64_to_uint8 (a3 >>^ 2ul)
    /\ b11 == uint64_to_uint8 (a3 >>^ 10ul)
    /\ b12 == uint64_to_uint8 (a3 >>^ 18ul)
    /\ b13 == uint64_to_uint8 a4
    /\ b14 == uint64_to_uint8 (a4 >>^ 8ul)
    /\ b15 == uint64_to_uint8 (a4 >>^ 16ul)) ))
        (ensures  ((Crypto.Symmetric.Poly1305.Bigint.eval ha a 5) % pow2 128
          = little_endian (as_seq hb b)))


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

let lemma_trunc1305 hb b ha a =
  lemma_little_endian_16 hb b;
  lemma_eval_5 ha a;
  lemma_norm_5 ha a;
  let a0 = get ha a 0 in let a1 = get ha a 1 in let a2 = get ha a 2 in let a3 = get ha a 3 in
  let a4 = get ha a 4 in
  let b0 = get hb b 0 in let b1 = get hb b 1 in let b2 = get hb b 2 in let b3 = get hb b 3 in
  let b4 = get hb b 4 in let b5 = get hb b 5 in let b6 = get hb b 6 in let b7 = get hb b 7 in
  let b8 = get hb b 8 in let b9 = get hb b 9 in let b10 = get hb b 10 in let b11 = get hb b 11 in
  let b12 = get hb b 12 in let b13 = get hb b 13 in let b14 = get hb b 14 in let b15 = get hb b 15 in
  let p8 = pow2 8 in let p16 = pow2 16 in let p24 = pow2 24 in
  let p32 = pow2 32 in let p40 = pow2 40 in let p48 = pow2 48 in let p56 = pow2 56 in
  let p64 = pow2 64 in let p72 = pow2 72 in let p80 = pow2 80 in let p88 = pow2 88 in
  let p96 = pow2 96 in let p104 = pow2 104 in let p112 = pow2 112 in let p120 = pow2 120 in
  lemma_b3 a0 a1;
  lemma_b6 a1 a2;
  lemma_b9 a2 a3;
  lemma_trunc1305_ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15;
  lemma_eval_mod a0 a1 a2 a3 a4


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val lemma_little_endian_4: h:HyperStack.mem -> b:Buffer.buffer U8.t{live h b /\ length b = 4} ->
  Lemma (little_endian (as_seq h b) = U8.(v (get h b 0) + pow2 8 * v (get h b 1)+ pow2 16 * v (get h b 2)+ pow2 24 * v (get h b 3)))
let lemma_little_endian_4 h b =
  let s = as_seq h b in
  lemma_little_endian_from_top s;
  lemma_little_endian_from_top_def s 4;
  lemma_little_endian_from_top_def s 3;
  lemma_little_endian_from_top_def s 2;
  lemma_little_endian_from_top_def s 1;
  lemma_little_endian_from_top_def s 0


val lemma_as_seq_sub:
  h:HyperStack.mem -> b:Buffer.buffer U8.t{live h b} -> i:U32.t -> len:U32.t{U32.v i + U32.v len <= length b} ->
  Lemma (let open FStar.UInt32 in
         Seq.slice (as_seq h b) (v i) (v i + v len) = as_seq h (Buffer.sub b i len))
let lemma_as_seq_sub h b i len = ()


val lemma_add_word_1:
  ha:HyperStack.mem ->
  a:Buffer.buffer U8.t{live ha a /\ length a = 16} ->
  a0:u64_32 -> a4:u64_32 -> a8:u64_32 -> a12:u64_32 ->
  Lemma (requires (
    let a' = sub a 4ul 4ul in let a'' = sub a 8ul 4ul in let a''' = sub a 12ul 4ul in
    let a = sub a 0ul 4ul in
    v a0 = U8.(v (get ha a 0) + pow2 8 * v (get ha a 1)+ pow2 16 * v (get ha a 2)+ pow2 24 * v (get ha a 3))
    /\ v a4 = U8.(v (get ha a' 0) + pow2 8 * v (get ha a' 1)+ pow2 16 * v (get ha a' 2)+ pow2 24 * v (get ha a' 3))
    /\ v a8 = U8.(v (get ha a'' 0) + pow2 8 * v (get ha a'' 1)+ pow2 16 * v (get ha a'' 2)+ pow2 24 * v (get ha a'' 3))
    /\ v a12 = U8.(v (get ha a''' 0) + pow2 8 * v (get ha a''' 1)+ pow2 16 * v (get ha a''' 2)+ pow2 24 * v (get ha a''' 3))))
    (ensures (little_endian (as_seq ha a) = v a0 + pow2 32 * v a4 + pow2 64 * v a8 + pow2 96 * v a12))
let lemma_add_word_1 ha a a0 a4 a8 a12 =
  lemma_as_seq_sub ha a 0ul  4ul;
  lemma_as_seq_sub ha a 4ul  4ul;
  lemma_as_seq_sub ha a 8ul  4ul;
  lemma_as_seq_sub ha a 12ul 4ul;
  lemma_little_endian_4 ha (sub a 0ul  4ul);
  lemma_little_endian_4 ha (sub a 4ul  4ul);
  lemma_little_endian_4 ha (sub a 8ul  4ul);
  lemma_little_endian_4 ha (sub a 12ul 4ul);
  let s = as_seq ha a in
  cut (v a0  = little_endian (Seq.slice s 0 4));
  cut (v a4  = little_endian (Seq.slice s 4 8));
  cut (v a8  = little_endian (Seq.slice s 8 12));
  cut (v a12 = little_endian (Seq.slice s 12 16));
  lemma_seq_append_16_to_4 s;
  let s04 = (Seq.slice s 0 4) in
  let s48 = (Seq.slice s 4 8) in
  let s812 = (Seq.slice s 8 12) in
  let s1216 = (Seq.slice s 12 16) in
  little_endian_append s04 s48;
  little_endian_append (Seq.append s04 s48) s812;
  little_endian_append (Seq.append (Seq.append s04 s48) s812) (s1216)


let eval_4 a0 a1 a2 a3 : GTot nat = v a0 + pow2 32 * v a1 + pow2 64 * v a2 + pow2 96 * v a3

#reset-options "--z3rlimit 100"

val lemma_add_word_2_2:
  a0:u64_32 -> a4:u64_32 -> a8:u64_32 -> a12:u64_32 ->
  b0:u64_32 -> b4:u64_32 -> b8:u64_32 -> b12:u64_32 ->
  Lemma (let z0 = v a0 + v b0 in
    let z1 = v a4 + v b4 + (z0 / pow2 32) in
    let z2 = v a8 + v b8 + (z1 / pow2 32) in
    let z3 = v a12 + v b12 + (z2 / pow2 32) in
    (z0 % pow2 32) + pow2 32 * (z1 % pow2 32) + pow2 64 * (z2 % pow2 32) + pow2 96 * (z3 % pow2 32)
    = ((z0 % pow2 32) + pow2 32 * (z1 % pow2 32) + pow2 64 * (z2 % pow2 32) + pow2 96 * z3) % pow2 128)
let lemma_add_word_2_2 a0 a1 a2 a3 b0 b1 b2 b3 =
  let z0 = v a0 + v b0 in
  let z1 = v a1 + v b1 + (z0 / pow2 32) in
  let z2 = v a2 + v b2 + (z1 / pow2 32) in
  let z3 = v a3 + v b3 + (z2 / pow2 32) in
  Math.Lemmas.lemma_mod_plus_distr_l (pow2 96 * z3) ((z0 % pow2 32) + pow2 32 * (z1 % pow2 32) + pow2 64 * (z2 % pow2 32)) (pow2 128);
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 z3 128 96;
  let r = (z0 % pow2 32) + pow2 32 * (z1 % pow2 32) + pow2 64 * (z2 % pow2 32) + pow2 96 * (z3 % pow2 32) in
  cut (((z0 % pow2 32) + pow2 32 * (z1 % pow2 32) + pow2 64 * (z2 % pow2 32) + pow2 96 * z3) % pow2 128 = r % pow2 128);
  lemma_mul_mod (z1 % pow2 32) (pow2 32);
  lemma_mul_mod (z2 % pow2 32) (pow2 32);
  lemma_mul_mod (z3 % pow2 32) (pow2 32);
  Math.Lemmas.pow2_plus 32 32;
  Math.Lemmas.pow2_plus 64 32;
  Math.Lemmas.pow2_plus 96 32;
  add_disjoint_bounded (z0 % pow2 32) (pow2 32 * (z1 % pow2 32)) 32 64;
  add_disjoint_bounded ((z0 % pow2 32)+(pow2 32 * (z1 % pow2 32)))
                             (pow2 64 * (z2 % pow2 32)) 64 96;
  add_disjoint_bounded ((z0 % pow2 32)+(pow2 32 * (z1 % pow2 32))+(pow2 64 * (z2 % pow2 32)))
                             (pow2 96 * (z3 % pow2 32)) 96 128;
  Math.Lemmas.modulo_lemma r (pow2 128)

#reset-options

val lemma_add_word_2_1:
  a0:u64_32 -> a4:u64_32 -> a8:u64_32 -> a12:u64_32 ->
  b0:u64_32 -> b4:u64_32 -> b8:u64_32 -> b12:u64_32 ->
  Lemma (let z0 = v a0 + v b0 in
    let z1 = v a4 + v b4 + (z0 / pow2 32) in
    let z2 = v a8 + v b8 + (z1 / pow2 32) in
    let z3 = v a12 + v b12 + (z2 / pow2 32) in
    (z0 % pow2 32) + pow2 32 * (z1 % pow2 32) + pow2 64 * (z2 % pow2 32) + pow2 96 * (z3 % pow2 32)
    = ((v a0 + v b0) + pow2 32 * (v a4 + v b4) + pow2 64 * (v a8 + v b8) + pow2 96 * (v a12 + v b12)) % pow2 128)
let lemma_add_word_2_1 a0 a4 a8 a12 b0 b4 b8 b12 =
  let z0 = v a0 + v b0 in
  let z1 = v a4 + v b4 + (z0 / pow2 32) in
  let z2 = v a8 + v b8 + (z1 / pow2 32) in
  let z3 = v a12 + v b12 + (z2 / pow2 32) in
  let ab0 = v a0 + v b0 in let ab1 = v a4 + v b4 in
  let ab2 = v a8 + v b8 in let ab3 = v a12 + v b12 in
  Math.Lemmas.lemma_div_mod (z0) (pow2 32);
  Math.Lemmas.distributivity_add_right (pow2 32) (v a4 + v b4) (z0 / pow2 32);
  cut (ab0 + pow2 32 * ab1 = (z0 % pow2 32) + pow2 32 * z1);
  Math.Lemmas.lemma_div_mod (z1) (pow2 32);
  Math.Lemmas.distributivity_add_right (pow2 64) (v a8 + v b8) (z1 / pow2 32);
  Math.Lemmas.distributivity_add_right (pow2 32) (z1 % pow2 32) (pow2 32 * (z1 / pow2 32));
  Math.Lemmas.pow2_plus 32 32;
  cut (ab0 + pow2 32 * ab1 + pow2 64 * ab2 = (z0 % pow2 32) + pow2 32 * (z1 % pow2 32)
                                             + pow2 64 * z2);
  Math.Lemmas.lemma_div_mod (z2) (pow2 32);
  Math.Lemmas.distributivity_add_right (pow2 96) (v a12 + v b12) (z2 / pow2 32);
  Math.Lemmas.distributivity_add_right (pow2 64) (z2 % pow2 32) (pow2 32 * (z2 / pow2 32));
  Math.Lemmas.pow2_plus 64 32;
  cut (ab0 + pow2 32 * ab1 + pow2 64 * ab2 + pow2 96 * ab3
           = (z0 % pow2 32) + pow2 32 * (z1 % pow2 32) + pow2 64 * (z2 % pow2 32) + pow2 96 * z3);
  lemma_add_word_2_2  a0 a4 a8 a12 b0 b4 b8 b12


val lemma_add_word_2:
  a0:u64_32 -> a4:u64_32 -> a8:u64_32 -> a12:u64_32 ->
  b0:u64_32 -> b4:u64_32 -> b8:u64_32 -> b12:u64_32 ->
  Lemma (let z0 = v a0 + v b0 in
    let z1 = v a4 + v b4 + (z0 / pow2 32) in
    let z2 = v a8 + v b8 + (z1 / pow2 32) in
    let z3 = v a12 + v b12 + (z2 / pow2 32) in
    (z0 % pow2 32) + pow2 32 * (z1 % pow2 32) + pow2 64 * (z2 % pow2 32) + pow2 96 * (z3 % pow2 32)
    = (eval_4 a0 a4 a8 a12 + eval_4 b0 b4 b8 b12) % pow2 128)
let lemma_add_word_2 a0 a4 a8 a12 b0 b4 b8 b12 =
  let va = eval_4 a0 a4 a8 a12 in let vb = eval_4 b0 b4 b8 b12 in
  let ab0 = v a0 + v b0 in let ab1 = v a4 + v b4 in
  let ab2 = v a8 + v b8 in let ab3 = v a12 + v b12 in
  Math.Lemmas.distributivity_add_right (pow2 32) (v a4) (v b4);
  Math.Lemmas.distributivity_add_right (pow2 64) (v a8) (v b8);
  Math.Lemmas.distributivity_add_right (pow2 96) (v a12) (v b12);
  cut (va + vb = ab0 + pow2 32 * ab1 + pow2 64 * ab2 + pow2 96 * ab3);
  lemma_add_word_2_1 a0 a4 a8 a12 b0 b4 b8 b12


let lemma_add_word_post a0 a4 a8 a12 b0 b4 b8 b12 ha (a:Buffer.buffer U8.t{live ha a})
                                                  hb (b:Buffer.buffer U8.t{live hb b})
  = let z0 = v a0 + v b0 in
    let z1 = v a4 + v b4 + (z0 / pow2 32) in
    let z2 = v a8 + v b8 + (z1 / pow2 32) in
    let z3 = v a12 + v b12 + (z2 / pow2 32) in
    (z0 % pow2 32) + pow2 32 * (z1 % pow2 32) + pow2 64 * (z2 % pow2 32) + pow2 96 * (z3 % pow2 32)
      = (little_endian (as_seq ha a) + little_endian (as_seq hb b)) % pow2 128


val lemma_add_word:
  ha:HyperStack.mem ->
  a:Buffer.buffer U8.t{live ha a /\ length a = 16} ->
  hb:HyperStack.mem ->
  b:Buffer.buffer U8.t{live hb b /\ length b = 16} ->
  a0:u64_32 -> a4:u64_32 -> a8:u64_32 -> a12:u64_32 ->
  b0:u64_32 -> b4:u64_32 -> b8:u64_32 -> b12:u64_32 ->
  Lemma (requires (
    let a' = sub a 4ul 4ul in let a'' = sub a 8ul 4ul in let a''' = sub a 12ul 4ul in
    let a = sub a 0ul 4ul in
    let b' = sub b 4ul 4ul in let b'' = sub b 8ul 4ul in let b''' = sub b 12ul 4ul in
    let b = sub b 0ul 4ul in
    v a0 = U8.(v (get ha a 0) + pow2 8 * v (get ha a 1)+ pow2 16 * v (get ha a 2)+ pow2 24 * v (get ha a 3))
    /\ v a4 = U8.(v (get ha a' 0) + pow2 8 * v (get ha a' 1)+ pow2 16 * v (get ha a' 2)+ pow2 24 * v (get ha a' 3))
    /\ v a8 = U8.(v (get ha a'' 0) + pow2 8 * v (get ha a'' 1)+ pow2 16 * v (get ha a'' 2)+ pow2 24 * v (get ha a'' 3))
    /\ v a12 = U8.(v (get ha a''' 0) + pow2 8 * v (get ha a''' 1)+ pow2 16 * v (get ha a''' 2)+ pow2 24 * v (get ha a''' 3))
    /\ v b0 = U8.(v (get hb b 0) + pow2 8 * v (get hb b 1)+ pow2 16 * v (get hb b 2)+ pow2 24 * v (get hb b 3))
    /\ v b4 = U8.(v (get hb b' 0) + pow2 8 * v (get hb b' 1)+ pow2 16 * v (get hb b' 2)+ pow2 24 * v (get hb b' 3))
    /\ v b8 = U8.(v (get hb b'' 0) + pow2 8 * v (get hb b'' 1)+ pow2 16 * v (get hb b'' 2)+ pow2 24 * v (get hb b'' 3))
    /\ v b12 = U8.(v (get hb b''' 0) + pow2 8 * v (get hb b''' 1)+ pow2 16 * v (get hb b''' 2)+ pow2 24 * v (get hb b''' 3))))
    (ensures (lemma_add_word_post a0 a4 a8 a12 b0 b4 b8 b12 ha a hb b))
let lemma_add_word ha a hb b a0 a4 a8 a12 b0 b4 b8 b12 =
  lemma_add_word_1 ha a a0 a4 a8 a12; lemma_add_word_1 hb b b0 b4 b8 b12;
  lemma_add_word_2 a0 a4 a8 a12 b0 b4 b8 b12


val lemma_add_word2_1:
  h0:HyperStack.mem ->
  h1:HyperStack.mem ->
  h2:HyperStack.mem ->
  h3:HyperStack.mem ->
  h4:HyperStack.mem ->
  b:Buffer.buffer U8.t{live h0 b /\ live h1 b /\ live h2 b /\ live h3 b /\ live h4 b /\ length b = 16} ->
  z0:U32.t -> z1:U32.t -> z2:U32.t -> z3:U32.t ->
  Lemma
    (requires (
      let b0 = sub b 0ul 4ul in
      let b1 = sub b 4ul 4ul in
      let b2 = sub b 8ul 4ul in
      let b3 = sub b 12ul 4ul in
      modifies_1 b0 h0 h1 /\ modifies_1 b1 h1 h2 /\ modifies_1 b2 h2 h3 /\ modifies_1 b3 h3 h4
      /\ U8.v (get h1 b0 0) = (U32.v z0) % pow2 8
      /\ U8.v (get h1 b0 1) = (U32.v z0 / pow2 8) % pow2 8
      /\ U8.v (get h1 b0 2) = (U32.v z0 / pow2 16) % pow2 8
      /\ U8.v (get h1 b0 3) = (U32.v z0 / pow2 24)  % pow2 8
      /\ U8.v (get h2 b1 0) = (U32.v z1) % pow2 8
      /\ U8.v (get h2 b1 1) = (U32.v z1 / pow2 8) % pow2 8
      /\ U8.v (get h2 b1 2) = (U32.v z1 / pow2 16) % pow2 8
      /\ U8.v (get h2 b1 3) = (U32.v z1 / pow2 24)  % pow2 8
      /\ U8.v (get h3 b2 0) = (U32.v z2) % pow2 8
      /\ U8.v (get h3 b2 1) = (U32.v z2 / pow2 8) % pow2 8
      /\ U8.v (get h3 b2 2) = (U32.v z2 / pow2 16) % pow2 8
      /\ U8.v (get h3 b2 3) = (U32.v z2 / pow2 24)  % pow2 8
      /\ U8.v (get h4 b3 0) = (U32.v z3) % pow2 8
      /\ U8.v (get h4 b3 1) = (U32.v z3 / pow2 8) % pow2 8
      /\ U8.v (get h4 b3 2) = (U32.v z3 / pow2 16) % pow2 8
      /\ U8.v (get h4 b3 3) = (U32.v z3 / pow2 24)  % pow2 8 ))
    (ensures (
      let b0 = sub b 0ul 4ul in
      let b1 = sub b 4ul 4ul in
      let b2 = sub b 8ul 4ul in
      let b3 = sub b 12ul 4ul in
      U8.v (get h4 b0 0) = (U32.v z0) % pow2 8
      /\ U8.v (get h4 b0 1) = (U32.v z0 / pow2 8) % pow2 8
      /\ U8.v (get h4 b0 2) = (U32.v z0 / pow2 16) % pow2 8
      /\ U8.v (get h4 b0 3) = (U32.v z0 / pow2 24)  % pow2 8
      /\ U8.v (get h4 b1 0) = (U32.v z1) % pow2 8
      /\ U8.v (get h4 b1 1) = (U32.v z1 / pow2 8) % pow2 8
      /\ U8.v (get h4 b1 2) = (U32.v z1 / pow2 16) % pow2 8
      /\ U8.v (get h4 b1 3) = (U32.v z1 / pow2 24)  % pow2 8
      /\ U8.v (get h4 b2 0) = (U32.v z2) % pow2 8
      /\ U8.v (get h4 b2 1) = (U32.v z2 / pow2 8) % pow2 8
      /\ U8.v (get h4 b2 2) = (U32.v z2 / pow2 16) % pow2 8
      /\ U8.v (get h4 b2 3) = (U32.v z2 / pow2 24)  % pow2 8
      /\ U8.v (get h4 b3 0) = (U32.v z3) % pow2 8
      /\ U8.v (get h4 b3 1) = (U32.v z3 / pow2 8) % pow2 8
      /\ U8.v (get h4 b3 2) = (U32.v z3 / pow2 16) % pow2 8
      /\ U8.v (get h4 b3 3) = (U32.v z3 / pow2 24)  % pow2 8 ))

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

let lemma_add_word2_1 h0 h1 h2 h3 h4 b z0 z1 z2 z3 =
  let b0 = sub b 0ul 4ul in
  let b1 = sub b 4ul 4ul in
  let b2 = sub b 8ul 4ul in
  let b3 = sub b 12ul 4ul in
  cut (disjoint b0 b1 /\ disjoint b0 b2 /\ disjoint b0 b3 /\ disjoint b1 b2 /\ disjoint b1 b3 /\ disjoint b2 b3);
  cut (live h0 b0 /\ live h0 b1 /\ live h0 b2 /\ live h0 b3);
  cut (live h1 b0 /\ live h1 b1 /\ live h1 b2 /\ live h1 b3);
  cut (live h2 b0 /\ live h2 b1 /\ live h2 b2 /\ live h2 b3);
  cut (live h3 b0 /\ live h3 b1 /\ live h3 b2 /\ live h3 b3);
  cut (live h4 b0 /\ live h4 b1 /\ live h4 b2 /\ live h4 b3);
  cut (equal h1 b0 h4 b0);
  cut (equal h2 b1 h4 b1);
  cut (equal h3 b2 h4 b2);
  cut (get h1 b0 0 == get h4 b0 0);
  cut (get h1 b0 1 == get h4 b0 1);
  cut (get h1 b0 2 == get h4 b0 2);
  cut (get h1 b0 3 == get h4 b0 3);
  cut (get h2 b1 0 == get h4 b1 0);
  cut (get h2 b1 1 == get h4 b1 1);
  cut (get h2 b1 2 == get h4 b1 2);
  cut (get h2 b1 3 == get h4 b1 3);
  cut (get h3 b2 0 == get h4 b2 0);
  cut (get h3 b2 1 == get h4 b2 1);
  cut (get h3 b2 2 == get h4 b2 2);
  cut (get h3 b2 3 == get h4 b2 3)


val lemma_add_word2_2_1: z:U32.t ->
  Lemma (((U32.v z) % pow2 8) + pow2 8 *  ((U32.v z / pow2 8) % pow2 8) + pow2 16 * ((U32.v z / pow2 16) % pow2 8) + pow2 24 * ((U32.v z / pow2 24) % pow2 8) = U32.v z)
let lemma_add_word2_2_1 z =
  let va32 = U32.v z in
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (U32.v z) 8 32;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (U32.v z) 16 32;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (U32.v z) 24 32;
  Math.Lemmas.lemma_div_mod (va32) (pow2 24);
  lemma_div_pow2_mod va32 32 24;
  cut (va32 = pow2 24 * ((va32 / pow2 24) % pow2 8) + (va32 % pow2 24));
  Math.Lemmas.lemma_div_mod (va32 % pow2 24) (pow2 16);
  Math.Lemmas.pow2_modulo_division_lemma_1 va32 16 24;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 va32 16 24;
  cut (va32 % pow2 24 = pow2 16 * ((va32/pow2 16)%pow2 8) + (va32 % pow2 16));
  Math.Lemmas.lemma_div_mod (va32 % pow2 16) (pow2 8);
  Math.Lemmas.pow2_modulo_division_lemma_1 va32 8 16;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 va32 8 16;
  cut (va32 % pow2 16 = pow2 8 * ((va32/pow2 8)%pow2 8) + (va32 % pow2 8))


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val lemma_add_word2_2:
  h:HyperStack.mem ->
  b:Buffer.buffer U8.t{live h b /\ length b = 16} ->
  z0:U32.t -> z1:U32.t -> z2:U32.t -> z3:U32.t ->
  Lemma
    (requires (
      let b0 = sub b 0ul 4ul in
      let b1 = sub b 4ul 4ul in
      let b2 = sub b 8ul 4ul in
      let b3 = sub b 12ul 4ul in
      U8.v (get h b0 0) = (U32.v z0) % pow2 8
      /\ U8.v (get h b0 1) = (U32.v z0 / pow2 8) % pow2 8
      /\ U8.v (get h b0 2) = (U32.v z0 / pow2 16) % pow2 8
      /\ U8.v (get h b0 3) = (U32.v z0 / pow2 24)  % pow2 8
      /\ U8.v (get h b1 0) = (U32.v z1) % pow2 8
      /\ U8.v (get h b1 1) = (U32.v z1 / pow2 8) % pow2 8
      /\ U8.v (get h b1 2) = (U32.v z1 / pow2 16) % pow2 8
      /\ U8.v (get h b1 3) = (U32.v z1 / pow2 24)  % pow2 8
      /\ U8.v (get h b2 0) = (U32.v z2) % pow2 8
      /\ U8.v (get h b2 1) = (U32.v z2 / pow2 8) % pow2 8
      /\ U8.v (get h b2 2) = (U32.v z2 / pow2 16) % pow2 8
      /\ U8.v (get h b2 3) = (U32.v z2 / pow2 24)  % pow2 8
      /\ U8.v (get h b3 0) = (U32.v z3) % pow2 8
      /\ U8.v (get h b3 1) = (U32.v z3 / pow2 8) % pow2 8
      /\ U8.v (get h b3 2) = (U32.v z3 / pow2 16) % pow2 8
      /\ U8.v (get h b3 3) = (U32.v z3 / pow2 24)  % pow2 8 ))
    (ensures (little_endian (as_seq h b) = U32.(v z0 + pow2 32 * v z1 + pow2 64 * v z2 + pow2 96 * v z3)))
let lemma_add_word2_2 ha a z0 z1 z2 z3 =
  lemma_as_seq_sub ha a 0ul  4ul;
  lemma_as_seq_sub ha a 4ul  4ul;
  lemma_as_seq_sub ha a 8ul  4ul;
  lemma_as_seq_sub ha a 12ul 4ul;
  lemma_little_endian_4 ha (sub a 0ul  4ul);
  lemma_little_endian_4 ha (sub a 4ul  4ul);
  lemma_little_endian_4 ha (sub a 8ul  4ul);
  lemma_little_endian_4 ha (sub a 12ul 4ul);
  lemma_add_word2_2_1 z0;
  lemma_add_word2_2_1 z1;
  lemma_add_word2_2_1 z2;
  lemma_add_word2_2_1 z3;
  let s = as_seq ha a in
  cut (U32.v z0  = little_endian (Seq.slice s 0 4));
  cut (U32.v z1  = little_endian (Seq.slice s 4 8));
  cut (U32.v z2  = little_endian (Seq.slice s 8 12));
  cut (U32.v z3 = little_endian (Seq.slice s 12 16));
  lemma_seq_append_16_to_4 s;
  let s04 = (Seq.slice s 0 4) in
  let s48 = (Seq.slice s 4 8) in
  let s812 = (Seq.slice s 8 12) in
  let s1216 = (Seq.slice s 12 16) in
  little_endian_append s04 s48;
  little_endian_append (Seq.append s04 s48) s812;
  little_endian_append (Seq.append (Seq.append s04 s48) s812) (s1216)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

val lemma_add_word2:
  h0:HyperStack.mem ->
  h1:HyperStack.mem ->
  h2:HyperStack.mem ->
  h3:HyperStack.mem ->
  h4:HyperStack.mem ->
  b:Buffer.buffer U8.t{live h0 b /\ live h1 b /\ live h2 b /\ live h3 b /\ live h4 b /\ length b = 16} ->
  z0:U32.t -> z1:U32.t -> z2:U32.t -> z3:U32.t ->
  Lemma
    (requires (
      let b0 = sub b 0ul 4ul in
      let b1 = sub b 4ul 4ul in
      let b2 = sub b 8ul 4ul in
      let b3 = sub b 12ul 4ul in
      modifies_1 b0 h0 h1 /\ modifies_1 b1 h1 h2 /\ modifies_1 b2 h2 h3 /\ modifies_1 b3 h3 h4
      /\ U8.v (get h1 b0 0) = (U32.v z0) % pow2 8
      /\ U8.v (get h1 b0 1) = (U32.v z0 / pow2 8) % pow2 8
      /\ U8.v (get h1 b0 2) = (U32.v z0 / pow2 16) % pow2 8
      /\ U8.v (get h1 b0 3) = (U32.v z0 / pow2 24)  % pow2 8
      /\ U8.v (get h2 b1 0) = (U32.v z1) % pow2 8
      /\ U8.v (get h2 b1 1) = (U32.v z1 / pow2 8) % pow2 8
      /\ U8.v (get h2 b1 2) = (U32.v z1 / pow2 16) % pow2 8
      /\ U8.v (get h2 b1 3) = (U32.v z1 / pow2 24)  % pow2 8
      /\ U8.v (get h3 b2 0) = (U32.v z2) % pow2 8
      /\ U8.v (get h3 b2 1) = (U32.v z2 / pow2 8) % pow2 8
      /\ U8.v (get h3 b2 2) = (U32.v z2 / pow2 16) % pow2 8
      /\ U8.v (get h3 b2 3) = (U32.v z2 / pow2 24)  % pow2 8
      /\ U8.v (get h4 b3 0) = (U32.v z3) % pow2 8
      /\ U8.v (get h4 b3 1) = (U32.v z3 / pow2 8) % pow2 8
      /\ U8.v (get h4 b3 2) = (U32.v z3 / pow2 16) % pow2 8
      /\ U8.v (get h4 b3 3) = (U32.v z3 / pow2 24)  % pow2 8 ))
    (ensures (little_endian (as_seq h4 b) = U32.(v z0 + pow2 32 * v z1 + pow2 64 * v z2 + pow2 96 * v z3)))
let lemma_add_word2 h0 h1 h2 h3 h4 b z0 z1 z2 z3 =
  lemma_add_word2_1 h0 h1 h2 h3 h4 b z0 z1 z2 z3;
  lemma_add_word2_2 h4 b z0 z1 z2 z3
