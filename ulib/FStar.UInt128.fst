module FStar.UInt128

open FStar.Mul

module UInt = FStar.UInt
module Seq = FStar.Seq
module BV = FStar.BitVector

module U32 = FStar.UInt32
module U64 = FStar.UInt64

module Math = FStar.Math.Lemmas

#reset-options "--max_fuel 0 --max_ifuel 0 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native"
#set-options "--normalize_pure_terms_for_extraction"

// This type gets a special treatment in KreMLin and its definition is never
// printed in the resulting C file.
type uint128 : Type0 = {
  low:U64.t;
  high:U64.t
}

let t = uint128

noextract
let v x = U64.v x.low + (U64.v x.high) * (pow2 64)

let div_mod (x: nat) (k: nat{k > 0}) : Lemma ((x / k) * k + x % k == x) = ()

let uint_to_t x =
  div_mod x (pow2 64);
  { low = U64.uint_to_t (x % (pow2 64)); high = U64.uint_to_t (x / (pow2 64)) }

let v_inj (x1: t) (x2: t) : Lemma (requires (v x1 == v x2)) (ensures x1 == x2) =
  assert (uint_to_t (v x1) == uint_to_t (v x2));
  assert (uint_to_t (v x1) == x1);
  assert (uint_to_t (v x2) == x2);
  ()

let constant_time_carry (a: U64.t) (b: U64.t) : Tot U64.t =
  let open U64 in
  // CONSTANT_TIME_CARRY macro
  // ((a ^ ((a ^ b) | ((a - b) ^ b))) >> (sizeof(a) * 8 - 1))
  // 63 = sizeof(a) * 8 - 1
  a ^^ ((a ^^ b) |^ ((a -%^ b) ^^ b)) >>^ U32.uint_to_t 63

// TODO: eventually we should prove this equivalence
assume
val constant_time_carry_ok: a: U64.t -> b: U64.t ->
  Lemma (constant_time_carry a b == (if U64.lt a b then U64.uint_to_t 1 else U64.uint_to_t 0))

let carry (a: U64.t) (b: U64.t)
  : Pure U64.t (requires True) (ensures (fun r -> U64.v r == (if U64.v a < U64.v b then 1 else 0))) =
  constant_time_carry_ok a b;
  constant_time_carry a b

let carry_sum_ok (a: U64.t) (b: U64.t)
  : Lemma (U64.v (carry (U64.add_mod a b) b) == (U64.v a + U64.v b) / (pow2 64)) = ()

let add (a: t) (b: t)
  : Pure t (requires (v a + v b < pow2 128)) (ensures (fun r -> v a + v b = v r)) =
  let l = U64.add_mod a.low b.low in
  carry_sum_ok a.low b.low;
  { low = l; high = U64.add (U64.add a.high b.high) (carry l b.low) }

let add_underspec (a: t) (b: t) =
  let l = U64.add_mod a.low b.low in
  if v a + v b < pow2 128 then carry_sum_ok a.low b.low;
  { low = l; high = U64.add_underspec (U64.add_underspec a.high b.high) (carry l b.low) }

val mod_mod: a: nat -> k: nat{k > 0} -> k': nat{k' > 0} -> Lemma ((a % k) % (k' * k) == a % k)
let mod_mod a k k' =
  assert (a % k < k);
  assert (a % k < k' * k)

let mod_spec (a: nat) (k: nat{k > 0}) : Lemma (a % k == a - (a / k) * k) = ()

val div_product: n: nat -> m1: nat{m1 > 0} -> m2: nat{m2 > 0} ->
  Lemma (n / (m1 * m2) == (n / m1) / m2)
let div_product n m1 m2 = Math.division_multiplication_lemma n m1 m2

val mul_div_cancel: n: nat -> k: nat{k > 0} -> Lemma ((n * k) / k == n)
let mul_div_cancel n k =
  Math.lemma_mod_plus 0 n k;
  assert ((n * k) % k == 0)

val mod_mul: n: nat -> k1: pos -> k2: pos -> Lemma ((n % k2) * k1 == (n * k1) % (k1 * k2))
let mod_mul n k1 k2 =
  mod_spec (n * k1) (k1 * k2);
  div_product (n * k1) k1 k2;
  mul_div_cancel n k1;
  Math.lemma_mul_sub_distr k1 n ((n / k2) * k2);
  mod_spec n k2

let mod_spec_rew_n (n: nat) (k: nat{k > 0}) : Lemma (n == (n / k) * k + n % k) = mod_spec n k

val mod_add: n1: nat -> n2: nat -> k: nat{k > 0} -> Lemma ((n1 % k + n2 % k) % k == (n1 + n2) % k)
let mod_add n1 n2 k = Math.modulo_distributivity n1 n2 k

val mod_add_small: n1: nat -> n2: nat -> k: nat{k > 0} ->
  Lemma (requires (n1 % k + n2 % k < k)) (ensures (n1 % k + n2 % k == (n1 + n2) % k))
let mod_add_small n1 n2 k =
  mod_add n1 n2 k;
  Math.small_modulo_lemma_1 (n1 % k + n2 % k) k

val pow2_plus_pat: n1: nat -> n2: nat ->
  Lemma (pow2 n1 * pow2 n2 == pow2 (n1 + n2)) [SMTPat (pow2 n1 * pow2 n2)]
let pow2_plus_pat n1 n2 = Math.pow2_plus n1 n2

val mod_mul_pat: n: nat -> k1: pos -> k2: pos ->
  Lemma ((n % k2) * k1 == (n * k1) % (k1 * k2)) [SMTPat ((n % k2) * k1)]
let mod_mul_pat n k1 k2 = mod_mul n k1 k2

val mod_mod_pat: a: nat -> k: nat{k > 0} -> k': nat{k' > 0} ->
  Lemma (requires (k' >= k)) (ensures ((a % k) % k' == a % k)) [SMTPat ((a % k) % k')]
let mod_mod_pat a k k' = assert (a % k < k)

#set-options "--z3rlimit 20"
let add_mod (a: t) (b: t) : Pure t (requires True) (ensures (fun r -> (v a + v b) % pow2 128 = v r)) =
  let l = U64.add_mod a.low b.low in
  let r = { low = l; high = U64.add_mod (U64.add_mod a.high b.high) (carry l b.low) } in
  let a_l = U64.v a.low in
  let a_h = U64.v a.high in
  let b_l = U64.v b.low in
  let b_h = U64.v b.high in
  carry_sum_ok a.low b.low;
  Math.lemma_mod_plus_distr_l (a_h + b_h) ((a_l + b_l) / (pow2 64)) (pow2 64);
  assert (U64.v r.high == (a_h + b_h + (a_l + b_l) / (pow2 64)) % pow2 64);
  // mod_mul (a_h + b_h + (a_l + b_l) / (pow2 64)) (pow2 64) (pow2 64);
  assert (U64.v r.high * pow2 64 ==
      (a_h * pow2 64 + b_h * pow2 64 + ((a_l + b_l) / (pow2 64)) * (pow2 64)) % pow2 128);
  assert (U64.v r.low == (U64.v r.low) % pow2 128); // mod_mod (U64.v r.low) (pow2 64) (pow2 64);
  mod_add_small (a_h * pow2 64 + b_h * pow2 64 + ((a_l + b_l) / (pow2 64)) * (pow2 64))
    ((a_l + b_l) % (pow2 64))
    (pow2 128);
  assert (U64.v r.low + U64.v r.high * pow2 64 ==
      (a_h * pow2 64 + b_h * pow2 64 + ((a_l + b_l) / (pow2 64)) * (pow2 64) +
        (a_l + b_l) % (pow2 64)) %
      pow2 128);
  mod_spec_rew_n (a_l + b_l) (pow2 64);
  assert (v r == (a_h * pow2 64 + b_h * pow2 64 + a_l + b_l) % pow2 128);
  r
#set-options "--z3rlimit 5"

let sub (a: t) (b: t) : Pure t (requires (v a - v b >= 0)) (ensures (fun r -> v r = v a - v b)) =
  let l = U64.sub_mod a.low b.low in
  { low = l; high = U64.sub (U64.sub a.high b.high) (carry a.low l) }

let sub_underspec (a: t) (b: t) =
  let l = U64.sub_mod a.low b.low in
  { low = l; high = U64.sub_underspec (U64.sub_underspec a.high b.high) (carry a.low l) }

let sub_mod_impl (a: t) (b: t) : t =
  let l = U64.sub_mod a.low b.low in
  { low = l; high = U64.sub_mod (U64.sub_mod a.high b.high) (carry a.low l) }

#set-options "--z3rlimit 20"
let sub_mod_pos_ok (a: t) (b: t)
  : Lemma (requires (v a - v b >= 0)) (ensures (v (sub_mod_impl a b) = v a - v b)) =
  assert (sub a b == sub_mod_impl a b);
  ()
#set-options "--z3rlimit 5"

val u64_diff_wrap: a: U64.t -> b: U64.t ->
  Lemma (requires (U64.v a < U64.v b))
    (ensures (U64.v (U64.sub_mod a b) == U64.v a - U64.v b + pow2 64))
let u64_diff_wrap a b = ()

val sub_mod_wrap1_ok: a: t -> b: t ->
  Lemma (requires (v a - v b < 0 /\ U64.v a.low < U64.v b.low))
    (ensures (v (sub_mod_impl a b) = v a - v b + pow2 128))
let sub_mod_wrap1_ok a b =
  // carry == 1 and subtraction in low wraps
  let l = U64.sub_mod a.low b.low in
  assert (U64.v (carry a.low l) == 1);
  u64_diff_wrap a.low b.low;
  // a.high <= b.high since v a < v b;
  // case split on equality and strictly less
  if U64.v a.high = U64.v b.high
  then ()
  else
    (u64_diff_wrap a.high b.high;
      ())

let sum_lt (a1: nat) (a2: nat) (b1: nat) (b2: nat)
  : Lemma (requires (a1 + a2 < b1 + b2 /\ a1 >= b1)) (ensures (a2 < b2)) = ()

let sub_mod_wrap2_ok (a: t) (b: t)
  : Lemma (requires (v a - v b < 0 /\ U64.v a.low >= U64.v b.low))
    (ensures (v (sub_mod_impl a b) = v a - v b + pow2 128)) =
  // carry == 0, subtraction in low is exact, but subtraction in high
  // must wrap since v a < v b
  let l = U64.sub_mod a.low b.low in
  let r = sub_mod_impl a b in
  assert (U64.v l == U64.v a.low - U64.v b.low);
  assert (U64.v (carry a.low l) == 0);
  sum_lt (U64.v a.low) (U64.v a.high * pow2 64) (U64.v b.low) (U64.v b.high * pow2 64);
  assert (U64.v (U64.sub_mod a.high b.high) == U64.v a.high - U64.v b.high + pow2 64);
  ()

let sub_mod_wrap_ok (a: t) (b: t)
  : Lemma (requires (v a - v b < 0)) (ensures (v (sub_mod_impl a b) = v a - v b + pow2 128)) =
  if U64.v a.low < U64.v b.low then sub_mod_wrap1_ok a b else sub_mod_wrap2_ok a b

#set-options "--z3rlimit 20"
let sub_mod (a: t) (b: t) : Pure t (requires True) (ensures (fun r -> v r = (v a - v b) % pow2 128)) =
  (if v a - v b >= 0 then sub_mod_pos_ok a b else sub_mod_wrap_ok a b);
  sub_mod_impl a b
#set-options "--z3rlimit 5"

val shift_bound: #n: nat -> num: UInt.uint_t n -> n': nat ->
  Lemma (num * pow2 n' <= pow2 (n' + n) - pow2 n')
let shift_bound #n num n' =
  Math.lemma_mult_le_right (pow2 n') num (pow2 n - 1);
  Math.distributivity_sub_left (pow2 n) 1 (pow2 n');
  Math.pow2_plus n' n

val append_uint: #n1: nat -> #n2: nat -> num1: UInt.uint_t n1 -> num2: UInt.uint_t n2 ->
  UInt.uint_t (n1 + n2)
let append_uint #n1 #n2 num1 num2 =
  shift_bound num2 n1;
  num1 + num2 * pow2 n1

val to_vec_append: 
  #n1: nat{n1 > 0} ->
  #n2: nat{n2 > 0} ->
  num1: UInt.uint_t n1 ->
  num2: UInt.uint_t n2 ->
  Lemma (UInt.to_vec (append_uint num1 num2) == Seq.append (UInt.to_vec num2) (UInt.to_vec num1))
let to_vec_append #n1 #n2 num1 num2 = UInt.append_lemma (UInt.to_vec num2) (UInt.to_vec num1)

let vec128 (a: t) : BV.bv_t 128 = UInt.to_vec #128 (v a)
let vec64 (a: U64.t) : BV.bv_t 64 = UInt.to_vec (U64.v a)

let to_vec_v (a: t) : Lemma (vec128 a == Seq.append (vec64 a.high) (vec64 a.low)) =
  to_vec_append (U64.v a.low) (U64.v a.high)

val logand_vec_append: 
  #n1: pos ->
  #n2: pos ->
  a1: BV.bv_t n1 ->
  b1: BV.bv_t n1 ->
  a2: BV.bv_t n2 ->
  b2: BV.bv_t n2 ->
  Lemma
  (Seq.append (BV.logand_vec a1 b1) (BV.logand_vec a2 b2) ==
    BV.logand_vec #(n1 + n2) (Seq.append a1 a2) (Seq.append b1 b2))
let logand_vec_append #n1 #n2 a1 b1 a2 b2 =
  Seq.lemma_eq_intro (Seq.append (BV.logand_vec a1 b1) (BV.logand_vec a2 b2))
    (BV.logand_vec #(n1 + n2) (Seq.append a1 a2) (Seq.append b1 b2))

let logand (a: t) (b: t)
  : Pure t (requires True) (ensures (fun r -> v r = UInt.logand #128 (v a) (v b))) =
  let r = { low = U64.logand a.low b.low; high = U64.logand a.high b.high } in
  to_vec_v r;
  assert (vec128 r == Seq.append (vec64 r.high) (vec64 r.low));
  logand_vec_append (vec64 a.high) (vec64 b.high) (vec64 a.low) (vec64 b.low);
  to_vec_v a;
  to_vec_v b;
  assert (vec128 r == BV.logand_vec (vec128 a) (vec128 b));
  r

val logxor_vec_append: 
  #n1: pos ->
  #n2: pos ->
  a1: BV.bv_t n1 ->
  b1: BV.bv_t n1 ->
  a2: BV.bv_t n2 ->
  b2: BV.bv_t n2 ->
  Lemma
  (Seq.append (BV.logxor_vec a1 b1) (BV.logxor_vec a2 b2) ==
    BV.logxor_vec #(n1 + n2) (Seq.append a1 a2) (Seq.append b1 b2))
let logxor_vec_append #n1 #n2 a1 b1 a2 b2 =
  Seq.lemma_eq_intro (Seq.append (BV.logxor_vec a1 b1) (BV.logxor_vec a2 b2))
    (BV.logxor_vec #(n1 + n2) (Seq.append a1 a2) (Seq.append b1 b2))

let logxor (a: t) (b: t)
  : Pure t (requires True) (ensures (fun r -> v r = UInt.logxor #128 (v a) (v b))) =
  let r = { low = U64.logxor a.low b.low; high = U64.logxor a.high b.high } in
  to_vec_v r;
  assert (vec128 r == Seq.append (vec64 r.high) (vec64 r.low));
  logxor_vec_append (vec64 a.high) (vec64 b.high) (vec64 a.low) (vec64 b.low);
  to_vec_v a;
  to_vec_v b;
  assert (vec128 r == BV.logxor_vec (vec128 a) (vec128 b));
  r

val logor_vec_append: 
  #n1: pos ->
  #n2: pos ->
  a1: BV.bv_t n1 ->
  b1: BV.bv_t n1 ->
  a2: BV.bv_t n2 ->
  b2: BV.bv_t n2 ->
  Lemma
  (Seq.append (BV.logor_vec a1 b1) (BV.logor_vec a2 b2) ==
    BV.logor_vec #(n1 + n2) (Seq.append a1 a2) (Seq.append b1 b2))
let logor_vec_append #n1 #n2 a1 b1 a2 b2 =
  Seq.lemma_eq_intro (Seq.append (BV.logor_vec a1 b1) (BV.logor_vec a2 b2))
    (BV.logor_vec #(n1 + n2) (Seq.append a1 a2) (Seq.append b1 b2))

let logor (a: t) (b: t)
  : Pure t (requires True) (ensures (fun r -> v r = UInt.logor #128 (v a) (v b))) =
  let r = { low = U64.logor a.low b.low; high = U64.logor a.high b.high } in
  to_vec_v r;
  assert (vec128 r == Seq.append (vec64 r.high) (vec64 r.low));
  logor_vec_append (vec64 a.high) (vec64 b.high) (vec64 a.low) (vec64 b.low);
  to_vec_v a;
  to_vec_v b;
  assert (vec128 r == BV.logor_vec (vec128 a) (vec128 b));
  r

val lognot_vec_append: #n1: pos -> #n2: pos -> a1: BV.bv_t n1 -> a2: BV.bv_t n2 ->
  Lemma
  (Seq.append (BV.lognot_vec a1) (BV.lognot_vec a2) == BV.lognot_vec #(n1 + n2) (Seq.append a1 a2))
let lognot_vec_append #n1 #n2 a1 a2 =
  Seq.lemma_eq_intro (Seq.append (BV.lognot_vec a1) (BV.lognot_vec a2))
    (BV.lognot_vec #(n1 + n2) (Seq.append a1 a2))

let lognot (a: t) : Pure t (requires True) (ensures (fun r -> v r = UInt.lognot #128 (v a))) =
  let r = { low = U64.lognot a.low; high = U64.lognot a.high } in
  to_vec_v r;
  assert (vec128 r == Seq.append (vec64 r.high) (vec64 r.low));
  lognot_vec_append (vec64 a.high) (vec64 a.low);
  to_vec_v a;
  assert (vec128 r == BV.lognot_vec (vec128 a));
  r

let mod_mul_cancel (n: nat) (k: nat{k > 0}) : Lemma ((n * k) % k == 0) =
  mod_spec (n * k) k;
  mul_div_cancel n k;
  ()

let shift_past_mod (n: nat) (k1: nat) (k2: nat{k2 >= k1}) : Lemma ((n * pow2 k2) % pow2 k1 == 0) =
  assert (k2 == (k2 - k1) + k1);
  Math.pow2_plus (k2 - k1) k1;
  Math.paren_mul_right n (pow2 (k2 - k1)) (pow2 k1);
  mod_mul_cancel (n * pow2 (k2 - k1)) (pow2 k1)

val mod_double: a: nat -> k: nat{k > 0} -> Lemma (a % k % k == a % k)
let mod_double a k = mod_mod a k 1

let shift_left_large_val (#n1: nat) (#n2: nat) (a1: UInt.uint_t n1) (a2: UInt.uint_t n2) (s: nat)
  : Lemma ((a1 + a2 * pow2 n1) * pow2 s == (a1 * pow2 s + a2 * pow2 (n1 + s))) =
  Math.distributivity_add_left a1 (a2 * pow2 n1) (pow2 s);
  Math.paren_mul_right a2 (pow2 n1) (pow2 s);
  Math.pow2_plus n1 s

#set-options "--z3rlimit 40"
let shift_left_large_lemma
  (#n1: nat) (#n2: nat) (a1: UInt.uint_t n1) (a2: UInt.uint_t n2) (s: nat{s >= n2})
  : Lemma (((a1 + a2 * pow2 n1) * pow2 s) % pow2 (n1 + n2) == (a1 * pow2 s) % pow2 (n1 + n2)) =
  shift_left_large_val a1 a2 s;
  mod_add (a1 * pow2 s) (a2 * pow2 (n1 + s)) (pow2 (n1 + n2));
  shift_past_mod a2 (n1 + n2) (n1 + s);
  mod_double (a1 * pow2 s) (pow2 (n1 + n2));
  ()
#set-options "--z3rlimit 5"

val shift_left_large_lemma_t: a: t -> s: nat ->
  Lemma (requires (s >= 64))
    (ensures ((v a * pow2 s) % pow2 128 == (U64.v a.low * pow2 s) % pow2 128))
let shift_left_large_lemma_t a s = shift_left_large_lemma #64 #64 (U64.v a.low) (U64.v a.high) s
private
let u32_64: n: U32.t{U32.v n == 64} = U32.uint_to_t 64

val div_pow2_diff: a: nat -> n1: nat -> n2: nat{n2 <= n1} ->
  Lemma (requires True) (ensures (a / pow2 (n1 - n2) == a * pow2 n2 / pow2 n1))
let div_pow2_diff a n1 n2 =
  Math.pow2_plus n2 (n1 - n2);
  assert (a * pow2 n2 / pow2 n1 == a * pow2 n2 / (pow2 n2 * pow2 (n1 - n2)));
  div_product (a * pow2 n2) (pow2 n2) (pow2 (n1 - n2));
  mul_div_cancel a (pow2 n2)

val mod_mul_pow2: n: nat -> e1: nat -> e2: nat ->
  Lemma ((n % pow2 e1) * pow2 e2 <= pow2 (e1 + e2) - pow2 e2)
let mod_mul_pow2 n e1 e2 =
  Math.lemma_mod_lt n (pow2 e1);
  Math.lemma_mult_le_right (pow2 e2) (n % pow2 e1) (pow2 e1 - 1);
  assert ((n % pow2 e1) * pow2 e2 <= pow2 e1 * pow2 e2 - pow2 e2);
  Math.pow2_plus e1 e2

let pow2_div_bound #b (n: UInt.uint_t b) (s: nat{s <= b}) : Lemma (n / pow2 s < pow2 (b - s)) =
  Math.lemma_div_lt n b s
#reset-options "--max_fuel 0 --max_ifuel 0 --smtencoding.elim_box true --smtencoding.l_arith_repr native --z3rlimit 40"
#set-options "--normalize_pure_terms_for_extraction"
let add_u64_shift_left (hi: U64.t) (lo: U64.t) (s: U32.t{U32.v s < 64})
  : Pure U64.t
    (requires (U32.v s <> 0))
    (ensures
      (fun r -> U64.v r = (U64.v hi * pow2 (U32.v s)) % pow2 64 + U64.v lo / pow2 (64 - U32.v s))) =
  let high = U64.shift_left hi s in
  let low = U64.shift_right lo (U32.sub u32_64 s) in
  let s = U32.v s in
  let high_n = (U64.v hi % pow2 (64 - s)) * pow2 s in
  let low_n = U64.v lo / pow2 (64 - s) in
  Math.pow2_plus (64 - s) s;
  mod_mul (U64.v hi) (pow2 s) (pow2 (64 - s));
  assert (U64.v high == high_n);
  assert (U64.v low == low_n);
  pow2_div_bound (U64.v lo) (64 - s);
  assert (low_n < pow2 s);
  mod_mul_pow2 (U64.v hi) (64 - s) s;
  U64.add high low
#reset-options "--max_fuel 0 --max_ifuel 0 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3cliopt 'smt.case_split=3'"
#set-options "--normalize_pure_terms_for_extraction"


let div_plus_multiple (a: nat) (b: nat) (k: pos)
  : Lemma (requires (a < k)) (ensures ((a + b * k) / k == b)) =
  Math.division_addition_lemma a k b;
  Math.small_division_lemma_1 a k

val div_add_small: n: nat -> m: nat -> k1: pos -> k2: pos ->
  Lemma (requires (n < k1)) (ensures (k1 * m / (k1 * k2) == (n + k1 * m) / (k1 * k2)))
let div_add_small n m k1 k2 =
  div_product (k1 * m) k1 k2;
  div_product (n + k1 * m) k1 k2;
  mul_div_cancel m k1;
  assert (k1 * m / k1 == m);
  div_plus_multiple n m k1
#set-options "--z3rlimit 5"

val add_mod_small: n: nat -> m: nat -> k1: pos -> k2: pos ->
  Lemma (requires (n < k1)) (ensures (n + (k1 * m) % (k1 * k2) == (n + k1 * m) % (k1 * k2)))
let add_mod_small n m k1 k2 =
  mod_spec (k1 * m) (k1 * k2);
  mod_spec (n + k1 * m) (k1 * k2);
  div_add_small n m k1 k2

let mod_then_mul_64 (n: nat) : Lemma ((n % pow2 64) * pow2 64 == n * pow2 64 % pow2 128) =
  Math.pow2_plus 64 64;
  mod_mul n (pow2 64) (pow2 64)

let mul_abc_to_acb (a: int) (b: int) (c: int) : Lemma (a * b * c == a * c * b) = ()

let add_u64_shift_left_respec (hi: U64.t) (lo: U64.t) (s: U32.t{U32.v s < 64})
  : Pure U64.t
    (requires (U32.v s <> 0))
    (ensures
      (fun r ->
          U64.v r * pow2 64 ==
          (U64.v hi * pow2 64) * pow2 (U32.v s) % pow2 128 +
          (U64.v lo * pow2 (U32.v s) / pow2 64) * pow2 64)) =
  let r = add_u64_shift_left hi lo s in
  let hi = U64.v hi in
  let lo = U64.v lo in
  let s = U32.v s in
  assert (U64.v r == hi * pow2 s % pow2 64 + lo / pow2 (64 - s)); // spec of add_u64_shift_left
  Math.distributivity_add_left (hi * pow2 s % pow2 64) (lo / pow2 (64 - s)) (pow2 64);
  mod_then_mul_64 (hi * pow2 s);
  assert ((hi * pow2 s % pow2 64) * pow2 64 == (hi * pow2 s * pow2 64) % pow2 128);
  div_pow2_diff lo 64 s;
  assert (lo / pow2 (64 - s) == lo * pow2 s / pow2 64);
  assert (U64.v r * pow2 64 == hi * pow2 s * pow2 64 % pow2 128 + (lo * pow2 s / pow2 64) * pow2 64);
  mul_abc_to_acb hi (pow2 s) (pow2 64);
  r

#set-options "--z3rlimit 40"
val add_mod_small': n: nat -> m: nat -> k: pos ->
  Lemma (requires (n + m % k < k)) (ensures (n + m % k == (n + m) % k))
let add_mod_small' n m k =
  Math.lemma_mod_lt (n + m % k) k;
  Math.modulo_lemma n k;
  mod_add n m k
#set-options "--z3rlimit 5"

let shift_t_val (a: t) (s: nat)
  : Lemma (v a * pow2 s == U64.v a.low * pow2 s + U64.v a.high * pow2 (64 + s)) =
  Math.pow2_plus 64 s;
  ()

val mul_mod_bound: n: nat -> s1: nat -> s2: nat{s2 >= s1} ->
  Lemma (n * pow2 s1 % pow2 s2 <= pow2 s2 - pow2 s1)
let mul_mod_bound n s1 s2 =
  // n * pow2 s1 % pow2 s2 == n % pow2 (s2-s1) * pow2 s1
  // n % pow2 (s2-s1) <= pow2 (s2-s1) - 1
  // n % pow2 (s2-s1) * pow2 s1 <= pow2 s2 - pow2 s1
  mod_mul n (pow2 s1) (pow2 (s2 - s1));
  // assert (n * pow2 s1 % pow2 s2 == n % pow2 (s2-s1) * pow2 s1);
  Math.lemma_mod_lt n (pow2 (s2 - s1));
  Math.lemma_mult_le_right (pow2 s1) (n % pow2 (s2 - s1)) (pow2 (s2 - s1) - 1);
  Math.pow2_plus (s2 - s1) s1

let add_lt_le (a: int) (a': int) (b: int) (b': int)
  : Lemma (requires (a < a' /\ b <= b')) (ensures (a + b < a' + b')) = ()

let u64_pow2_bound (a: UInt.uint_t 64) (s: nat) : Lemma (a * pow2 s < pow2 (64 + s)) =
  Math.pow2_plus 64 s;
  Math.lemma_mult_le_right (pow2 s) a (pow2 64)

#set-options "--z3rlimit 20"
let shift_t_mod_val' (a: t) (s: nat{s < 64})
  : Lemma
  ((v a * pow2 s) % pow2 128 == U64.v a.low * pow2 s + U64.v a.high * pow2 (64 + s) % pow2 128) =
  let a_l = U64.v a.low in
  let a_h = U64.v a.high in
  u64_pow2_bound a_l s;
  mul_mod_bound a_h (64 + s) 128;
  // assert (a_h * pow2 (64+s) % pow2 128 <= pow2 128 - pow2 (64+s));
  add_lt_le (a_l * pow2 s)
    (pow2 (64 + s))
    (a_h * pow2 (64 + s) % pow2 128)
    (pow2 128 - pow2 (64 + s));
  add_mod_small' (a_l * pow2 s) (a_h * pow2 (64 + s)) (pow2 128);
  shift_t_val a s;
  ()
#set-options "--z3rlimit 5"

let shift_t_mod_val (a: t) (s: nat{s < 64})
  : Lemma
  ((v a * pow2 s) % pow2 128 == U64.v a.low * pow2 s + (U64.v a.high * pow2 64) * pow2 s % pow2 128) =
  let a_l = U64.v a.low in
  let a_h = U64.v a.high in
  shift_t_mod_val' a s;
  Math.pow2_plus 64 s;
  Math.paren_mul_right a_h (pow2 64) (pow2 s);
  ()

#reset-options "--normalize_pure_terms_for_extraction"
#set-options "--z3rlimit 300"
let shift_left_small (a: t) (s: U32.t)
  : Pure t (requires (U32.v s < 64)) (ensures (fun r -> v r = (v a * pow2 (U32.v s)) % pow2 128)) =
  if U32.eq s 0ul
  then a
  else
    let r = { low = U64.shift_left a.low s; high = add_u64_shift_left_respec a.high a.low s } in
    let s = U32.v s in
    let a_l = U64.v a.low in
    let a_h = U64.v a.high in
    mod_spec_rew_n (a_l * pow2 s) (pow2 64);
    shift_t_mod_val a s;
    r

val shift_left_large: a: t -> s: U32.t{U32.v s >= 64 /\ U32.v s < 128} ->
  r: t{v r = (v a * pow2 (U32.v s)) % pow2 128}
#reset-options "--max_fuel 0 --max_ifuel 0"
#set-options "--normalize_pure_terms_for_extraction --z3rlimit 150"
let shift_left_large a s =
  let h_shift = U32.sub s u32_64 in
  assert (U32.v h_shift < 64);
  let r = { low = U64.uint_to_t 0; high = U64.shift_left a.low h_shift } in
  assert (U64.v r.high == (U64.v a.low * pow2 (U32.v s - 64)) % pow2 64);
  mod_mul (U64.v a.low * pow2 (U32.v s - 64)) (pow2 64) (pow2 64);
  Math.pow2_plus (U32.v s - 64) 64;
  assert (U64.v r.high * pow2 64 == (U64.v a.low * pow2 (U32.v s)) % pow2 128);
  shift_left_large_lemma_t a (U32.v s);
  r
#set-options "--z3rlimit 128 --max_fuel 0 --max_ifuel 0"

let shift_left a s = if (U32.lt s u32_64) then shift_left_small a s else shift_left_large a s

let add_u64_shift_right (hi: U64.t) (lo: U64.t) (s: U32.t{U32.v s < 64})
  : Pure U64.t
    (requires (U32.v s <> 0))
    (ensures
      (fun r -> U64.v r == U64.v lo / pow2 (U32.v s) + U64.v hi * pow2 (64 - U32.v s) % pow2 64)) =
  let low = U64.shift_right lo s in
  let high = U64.shift_left hi (U32.sub u32_64 s) in
  let s = U32.v s in
  let low_n = U64.v lo / pow2 s in
  let high_n = (U64.v hi % pow2 s) * pow2 (64 - s) in
  Math.pow2_plus (64 - s) s;
  mod_mul (U64.v hi) (pow2 (64 - s)) (pow2 s);
  assert (U64.v high == high_n);
  pow2_div_bound (U64.v lo) s;
  assert (low_n < pow2 (64 - s));
  mod_mul_pow2 (U64.v hi) s (64 - s);
  U64.add low high

#set-options "--z3rlimit 10"
val mul_pow2_diff: a: nat -> n1: nat -> n2: nat{n2 <= n1} ->
  Lemma (a * pow2 (n1 - n2) == a * pow2 n1 / pow2 n2)
let mul_pow2_diff a n1 n2 =
  Math.paren_mul_right a (pow2 (n1 - n2)) (pow2 n2);
  mul_div_cancel (a * pow2 (n1 - n2)) (pow2 n2);
  Math.pow2_plus (n1 - n2) n2

let add_u64_shift_right_respec (hi: U64.t) (lo: U64.t) (s: U32.t{U32.v s < 64})
  : Pure U64.t
    (requires (U32.v s <> 0))
    (ensures
      (fun r -> U64.v r == U64.v lo / pow2 (U32.v s) + U64.v hi * pow2 64 / pow2 (U32.v s) % pow2 64
      )) =
  let r = add_u64_shift_right hi lo s in
  let s = U32.v s in
  mul_pow2_diff (U64.v hi) 64 s;
  r

let mul_div_spec (n: nat) (k: pos) : Lemma ((n / k) * k == n - n % k) = ()

let mul_distr_sub (n1: nat) (n2: nat) (k: nat) : Lemma ((n1 - n2) * k == n1 * k - n2 * k) = ()

val div_product_comm: n1: nat -> k1: pos -> k2: pos -> Lemma (n1 / k1 / k2 == n1 / k2 / k1)
let div_product_comm n1 k1 k2 =
  div_product n1 k1 k2;
  div_product n1 k2 k1

val shift_right_reconstruct: a_h: UInt.uint_t 64 -> s: nat{s < 64} ->
  Lemma (a_h * pow2 (64 - s) == (a_h / pow2 s) * pow2 64 + a_h * pow2 64 / pow2 s % pow2 64)
let shift_right_reconstruct a_h s =
  mul_pow2_diff a_h 64 s;
  mod_spec_rew_n (a_h * pow2 (64 - s)) (pow2 64);
  div_product_comm (a_h * pow2 64) (pow2 s) (pow2 64);
  mul_div_cancel a_h (pow2 64);
  assert ((a_h / pow2 s) * pow2 64 == (a_h * pow2 64 / pow2 s / pow2 64) * pow2 64);
  ()

val u128_div_pow2: a: t -> s: nat{s < 64} ->
  Lemma (v a / pow2 s == U64.v a.low / pow2 s + U64.v a.high * pow2 (64 - s))
let u128_div_pow2 a s =
  Math.pow2_plus (64 - s) s;
  Math.paren_mul_right (U64.v a.high) (pow2 (64 - s)) (pow2 s);
  Math.division_addition_lemma (U64.v a.low) (pow2 s) (U64.v a.high * pow2 (64 - s))

let shift_right_small (a: t) (s: U32.t{U32.v s < 64})
  : Pure t (requires True) (ensures (fun r -> v r == v a / pow2 (U32.v s))) =
  if U32.eq s 0ul
  then a
  else
    let r = { low = add_u64_shift_right_respec a.high a.low s; high = U64.shift_right a.high s } in
    let a_h = U64.v a.high in
    let a_l = U64.v a.low in
    let s = U32.v s in
    shift_right_reconstruct a_h s;
    assert (v r == a_h * pow2 (64 - s) + a_l / pow2 s);
    u128_div_pow2 a s;
    r

let shift_right_large (a: t) (s: U32.t{U32.v s >= 64 /\ U32.v s < 128})
  : Pure t (requires True) (ensures (fun r -> v r == v a / pow2 (U32.v s))) =
  let r = { high = U64.uint_to_t 0; low = U64.shift_right a.high (U32.sub s u32_64) } in
  let s = U32.v s in
  Math.pow2_plus 64 (s - 64);
  div_product (v a) (pow2 64) (pow2 (s - 64));
  assert (v a / pow2 s == v a / pow2 64 / pow2 (s - 64));
  div_plus_multiple (U64.v a.low) (U64.v a.high) (pow2 64);
  r

let shift_right (a: t) (s: U32.t)
  : Pure t (requires (U32.v s < 128)) (ensures (fun r -> v r == v a / pow2 (U32.v s))) =
  if U32.lt s u32_64 then shift_right_small a s else shift_right_large a s

let eq (a: t) (b: t) = U64.eq a.low b.low && U64.eq a.high b.high
let gt (a: t) (b: t) = U64.gt a.high b.high || (U64.eq a.high b.high && U64.gt a.low b.low)
let lt (a: t) (b: t) = U64.lt a.high b.high || (U64.eq a.high b.high && U64.lt a.low b.low)
let gte (a: t) (b: t) = U64.gt a.high b.high || (U64.eq a.high b.high && U64.gte a.low b.low)
let lte (a: t) (b: t) = U64.lt a.high b.high || (U64.eq a.high b.high && U64.lte a.low b.low)

let u64_logand_comm (a: U64.t) (b: U64.t) : Lemma (U64.logand a b == U64.logand b a) =
  UInt.logand_commutative (U64.v a) (U64.v b)

val u64_and_0: a: U64.t -> b: U64.t ->
  Lemma (U64.v b = 0 ==> U64.v (U64.logand a b) = 0) [SMTPat (U64.logand a b)]
let u64_and_0 a b = UInt.logand_lemma_1 (U64.v a)

let u64_0_and (a: U64.t) (b: U64.t)
  : Lemma (U64.v a = 0 ==> U64.v (U64.logand a b) = 0) [SMTPat (U64.logand a b)] =
  u64_logand_comm a b

val u64_1s_and: a: U64.t -> b: U64.t ->
  Lemma (U64.v a = pow2 64 - 1 /\ U64.v b = pow2 64 - 1 ==> U64.v (U64.logand a b) = pow2 64 - 1)
    [SMTPat (U64.logand a b)]
let u64_1s_and a b = UInt.logand_lemma_2 (U64.v a)

let eq_mask (a: t) (b: t)
  : Pure t
    (requires True)
    (ensures (fun r -> (v a = v b ==> v r = pow2 128 - 1) /\ (v a <> v b ==> v r = 0))) =
  let mask = U64.logand (U64.eq_mask a.low b.low) (U64.eq_mask a.high b.high) in
  { low = mask; high = mask }
private
let gte_characterization (a: t) (b: t)
  : Lemma
  (v a >= v b ==>
    U64.v a.high > U64.v b.high \/ (U64.v a.high = U64.v b.high /\ U64.v a.low >= U64.v b.low)) = ()
private
let lt_characterization (a: t) (b: t)
  : Lemma
  (v a < v b ==>
    U64.v a.high < U64.v b.high \/ (U64.v a.high = U64.v b.high /\ U64.v a.low < U64.v b.low)) = ()

let u64_logor_comm (a: U64.t) (b: U64.t) : Lemma (U64.logor a b == U64.logor b a) =
  UInt.logor_commutative (U64.v a) (U64.v b)

val u64_or_1: a: U64.t -> b: U64.t ->
  Lemma (U64.v b = pow2 64 - 1 ==> U64.v (U64.logor a b) = pow2 64 - 1) [SMTPat (U64.logor a b)]
let u64_or_1 a b = UInt.logor_lemma_2 (U64.v a)

let u64_1_or (a: U64.t) (b: U64.t)
  : Lemma (U64.v a = pow2 64 - 1 ==> U64.v (U64.logor a b) = pow2 64 - 1) [SMTPat (U64.logor a b)] =
  u64_logor_comm a b

val u64_or_0: a: U64.t -> b: U64.t ->
  Lemma (U64.v a = 0 /\ U64.v b = 0 ==> U64.v (U64.logor a b) = 0) [SMTPat (U64.logor a b)]
let u64_or_0 a b = UInt.logor_lemma_1 (U64.v a)

val u64_not_0: a: U64.t ->
  Lemma (U64.v a = 0 ==> U64.v (U64.lognot a) = pow2 64 - 1) [SMTPat (U64.lognot a)]
let u64_not_0 a = UInt.lognot_lemma_1 #64

val u64_not_1: a: U64.t ->
  Lemma (U64.v a = pow2 64 - 1 ==> U64.v (U64.lognot a) = 0) [SMTPat (U64.lognot a)]
let u64_not_1 a = UInt.nth_lemma (UInt.lognot #64 (UInt.ones 64)) (UInt.zero 64)

let gte_mask (a: t) (b: t)
  : Pure t
    (requires True)
    (ensures (fun r -> (v a >= v b ==> v r = pow2 128 - 1) /\ (v a < v b ==> v r = 0))) =
  let mask_hi_gte =
    U64.logand (U64.gte_mask a.high b.high) (U64.lognot (U64.eq_mask a.high b.high))
  in
  let mask_lo_gte = U64.logand (U64.eq_mask a.high b.high) (U64.gte_mask a.low b.low) in
  let mask = U64.logor mask_hi_gte mask_lo_gte in
  gte_characterization a b;
  lt_characterization a b;
  { low = mask; high = mask }

let uint64_to_uint128 (a: U64.t) = { low = a; high = U64.uint_to_t 0 }

let uint128_to_uint64 (a: t) : b: U64.t{U64.v b == v a % pow2 64} = a.low

inline_for_extraction
let u64_l32_mask: x: U64.t{U64.v x == pow2 32 - 1} = U64.uint_to_t 0xffffffff

let u64_mod_32 (a: U64.t)
  : Pure U64.t (requires True) (ensures (fun r -> U64.v r = U64.v a % pow2 32)) =
  UInt.logand_mask (U64.v a) 32;
  U64.logand a u64_l32_mask

let u64_32_digits (a: U64.t) : Lemma ((U64.v a / pow2 32) * pow2 32 + U64.v a % pow2 32 == U64.v a) =
  div_mod (U64.v a) (pow2 32)

val mul32_digits: x: UInt.uint_t 64 -> y: UInt.uint_t 32 ->
  Lemma (x * y == ((x / pow2 32) * y) * pow2 32 + (x % pow2 32) * y)
let mul32_digits x y = ()

let u32_32: x: U32.t{U32.v x == 32} = U32.uint_to_t 32

let u32_combine (hi: U64.t) (lo: U64.t)
  : Pure U64.t
    (requires (U64.v lo < pow2 32))
    (ensures (fun r -> U64.v r = (U64.v hi % pow2 32) * pow2 32 + U64.v lo)) =
  U64.add lo (U64.shift_left hi u32_32)

// generalization of Math.lemma_mult_le_left (relaxed bounds on arguments)
val lemma_mult_le_left: a: nat -> b: int -> c: int ->
  Lemma (requires (b <= c)) (ensures (a * b <= a * c))
let lemma_mult_le_left a b c = ()

let product_bound (a: nat) (b: nat) (k: pos)
  : Lemma (requires (a < k /\ b < k)) (ensures a * b <= k * k - 2 * k + 1) =
  Math.lemma_mult_le_right b a (k - 1);
  lemma_mult_le_left (k - 1) b (k - 1)

val uint_product_bound: #n: nat -> a: UInt.uint_t n -> b: UInt.uint_t n ->
  Lemma (a * b <= pow2 (2 * n) - 2 * (pow2 n) + 1)
let uint_product_bound #n a b =
  product_bound a b (pow2 n);
  Math.pow2_plus n n

val u32_product_bound: a: nat{a < pow2 32} -> b: nat{b < pow2 32} ->
  Lemma (UInt.size (a * b) 64 /\ a * b < pow2 64 - pow2 32 - 1)
let u32_product_bound a b = uint_product_bound #32 a b

let mul32 x y =
  let x0 = u64_mod_32 x in
  let x1 = U64.shift_right x u32_32 in
  u32_product_bound (U64.v x0) (U32.v y);
  let x0y = U64.mul x0 (FStar.Int.Cast.uint32_to_uint64 y) in
  let x0yl = u64_mod_32 x0y in
  let x0yh = U64.shift_right x0y u32_32 in
  u32_product_bound (U64.v x1) (U32.v y);
  // not in the original C code
  let x1y' = U64.mul x1 (FStar.Int.Cast.uint32_to_uint64 y) in
  let x1y = U64.add x1y' x0yh in
  // correspondence with C:
  // r0 = r.low
  // r0 is written using u32_combine hi lo = lo + hi << 32
  // r1 = r.high
  let r = { low = u32_combine x1y x0yl; high = U64.shift_right x1y u32_32 } in
  u64_32_digits x;
  assert (U64.v x0y == U64.v x0 * U32.v y); //assert (U64.v x == U64.v x1 * pow2 32 + U64.v x0);
  u64_32_digits x0y;
  //assert (U64.v x0y == U64.v x0yh * pow2 32 + U64.v x0yl);
  assert (U64.v x1y' == (U64.v x / pow2 32) * U32.v y);
  mul32_digits (U64.v x) (U32.v y);
  assert (U64.v x * U32.v y == U64.v x1y' * pow2 32 + U64.v x0y);
  r

let l32 (x: UInt.uint_t 64) : UInt.uint_t 32 = x % pow2 32
let h32 (x: UInt.uint_t 64) : UInt.uint_t 32 = x / pow2 32

val mul32_bound: x: UInt.uint_t 32 -> y: UInt.uint_t 32 ->
  n: UInt.uint_t 64 {n < pow2 64 - pow2 32 - 1 /\ n == x * y}
let mul32_bound x y =
  u32_product_bound x y;
  x * y

let pll (x: U64.t) (y: U64.t) : n: UInt.uint_t 64 {n < pow2 64 - pow2 32 - 1} =
  mul32_bound (l32 (U64.v x)) (l32 (U64.v y))
let plh (x: U64.t) (y: U64.t) : n: UInt.uint_t 64 {n < pow2 64 - pow2 32 - 1} =
  mul32_bound (l32 (U64.v x)) (h32 (U64.v y))
let phl (x: U64.t) (y: U64.t) : n: UInt.uint_t 64 {n < pow2 64 - pow2 32 - 1} =
  mul32_bound (h32 (U64.v x)) (l32 (U64.v y))
let phh (x: U64.t) (y: U64.t) : n: UInt.uint_t 64 {n < pow2 64 - pow2 32 - 1} =
  mul32_bound (h32 (U64.v x)) (h32 (U64.v y))

let pll_l (x: U64.t) (y: U64.t) : UInt.uint_t 32 = l32 (pll x y)
let pll_h (x: U64.t) (y: U64.t) : UInt.uint_t 32 = h32 (pll x y)

let mul_wide_low (x: U64.t) (y: U64.t) =
  (plh x y + (phl x y + pll_h x y) % pow2 32) * pow2 32 % pow2 64 + pll_l x y

let mul_wide_high (x: U64.t) (y: U64.t) =
  phh x y + (phl x y + pll_h x y) / pow2 32 + (plh x y + (phl x y + pll_h x y) % pow2 32) / pow2 32

let mul_wide_impl_t' (x: U64.t) (y: U64.t)
  : Pure (tuple4 U64.t U64.t U64.t U64.t)
    (requires True)
    (ensures
      (fun r ->
          let u1, w3, x', t' = r in
          U64.v u1 == U64.v x % pow2 32 /\ U64.v w3 == pll_l x y /\ U64.v x' == h32 (U64.v x) /\
          U64.v t' == phl x y + pll_h x y)) =
  let u1 = u64_mod_32 x in
  let v1 = u64_mod_32 y in
  u32_product_bound (U64.v u1) (U64.v v1);
  let t = U64.mul u1 v1 in
  assert (U64.v t == pll x y);
  let w3 = u64_mod_32 t in
  assert (U64.v w3 == pll_l x y);
  let k = U64.shift_right t u32_32 in
  assert (U64.v k == pll_h x y);
  let x' = U64.shift_right x u32_32 in
  assert (U64.v x' == h32 (U64.v x));
  u32_product_bound (U64.v x') (U64.v v1);
  let t' = U64.add (U64.mul x' v1) k in
  (u1, w3, x', t')

// similar to u32_combine, but use % 2^64 * 2^32
let u32_combine' (hi: U64.t) (lo: U64.t)
  : Pure U64.t
    (requires (U64.v lo < pow2 32))
    (ensures (fun r -> U64.v r = U64.v hi * pow2 32 % pow2 64 + U64.v lo)) =
  U64.add lo (U64.shift_left hi u32_32)

#set-options "--z3rlimit 20"
let mul_wide_impl (x: U64.t) (y: U64.t)
  : Tot (r: t{U64.v r.low == mul_wide_low x y /\ U64.v r.high == mul_wide_high x y % pow2 64}) =
  let u1, w3, x', t' = mul_wide_impl_t' x y in
  let k' = u64_mod_32 t' in
  let w1 = U64.shift_right t' u32_32 in
  assert (U64.v w1 == (phl x y + pll_h x y) / pow2 32);
  let y' = U64.shift_right y u32_32 in
  assert (U64.v y' == h32 (U64.v y));
  u32_product_bound (U64.v u1) (U64.v y');
  let t'' = U64.add (U64.mul u1 y') k' in
  assert (U64.v t'' == plh x y + (phl x y + pll_h x y) % pow2 32);
  let k'' = U64.shift_right t'' u32_32 in
  assert (U64.v k'' == (plh x y + (phl x y + pll_h x y) % pow2 32) / pow2 32);
  u32_product_bound (U64.v x') (U64.v y');
  mod_mul_pow2 (U64.v t'') 32 64;
  let r0 = u32_combine' t'' w3 in
  // let r0 = U64.add (U64.shift_left t'' u32_32) w3 in
  assert (U64.v r0 == (plh x y + (phl x y + pll_h x y) % pow2 32) * pow2 32 % pow2 64 + pll_l x y);
  let xy_w1 = U64.add (U64.mul x' y') w1 in
  assert (U64.v xy_w1 == phh x y + (phl x y + pll_h x y) / pow2 32);
  let r1 = U64.add_mod xy_w1 k'' in
  assert (U64.v r1 ==
      (phh x y + (phl x y + pll_h x y) / pow2 32 +
        (plh x y + (phl x y + pll_h x y) % pow2 32) / pow2 32) %
      pow2 64);
  let r = { low = r0; high = r1 } in
  r
#set-options "--z3rlimit 5"

let product_sums (a: nat) (b: nat) (c: nat) (d: nat)
  : Lemma ((a + b) * (c + d) == a * c + a * d + b * c + b * d) = ()

val u64_32_product: 
  xl: UInt.uint_t 32 ->
  xh: UInt.uint_t 32 ->
  yl: UInt.uint_t 32 ->
  yh: UInt.uint_t 32 ->
  Lemma
  ((xl + xh * pow2 32) * (yl + yh * pow2 32) ==
    xl * yl + (xl * yh) * pow2 32 + (xh * yl) * pow2 32 + (xh * yh) * pow2 64)
let u64_32_product xl xh yl yh =
  product_sums xl (xh * pow2 32) yl (yh * pow2 32);
  mul_abc_to_acb xh (pow2 32) yl;
  assert (xl * (yh * pow2 32) == (xl * yh) * pow2 32);
  Math.pow2_plus 32 32;
  assert ((xh * pow2 32) * (yh * pow2 32) == (xh * yh) * pow2 64)

let product_expand (x: U64.t) (y: U64.t)
  : Lemma
  (U64.v x * U64.v y == phh x y * pow2 64 + (plh x y + phl x y + pll_h x y) * pow2 32 + pll_l x y) =
  assert (U64.v x == l32 (U64.v x) + h32 (U64.v x) * pow2 32);
  assert (U64.v y == l32 (U64.v y) + h32 (U64.v y) * pow2 32);
  u64_32_product (l32 (U64.v x)) (h32 (U64.v x)) (l32 (U64.v y)) (h32 (U64.v y))

let product_low_expand (x: U64.t) (y: U64.t)
  : Lemma
  ((U64.v x * U64.v y) % pow2 64 ==
    ((plh x y + phl x y + pll_h x y) * pow2 32 + pll_l x y) % pow2 64) =
  product_expand x y;
  Math.lemma_mod_plus ((plh x y + phl x y + pll_h x y) * pow2 32 + pll_l x y) (phh x y) (pow2 64)

let add_mod_then_mod (n: nat) (m: nat) (k: pos) : Lemma ((n + m % k) % k == (n + m) % k) =
  mod_add n m k;
  mod_add n (m % k) k;
  mod_double m k

let shift_add (n: nat) (m: nat{m < pow2 32})
  : Lemma (n * pow2 32 % pow2 64 + m == (n * pow2 32 + m) % pow2 64) =
  add_mod_small' m (n * pow2 32) (pow2 64)

let mul_wide_low_ok (x: U64.t) (y: U64.t)
  : Lemma (mul_wide_low x y == (U64.v x * U64.v y) % pow2 64) =
  Math.pow2_plus 32 32;
  mod_mul (plh x y + (phl x y + pll_h x y) % pow2 32) (pow2 32) (pow2 32);
  assert (mul_wide_low x y ==
      ((plh x y + (phl x y + pll_h x y) % pow2 32) % pow2 32) * pow2 32 + pll_l x y);
  add_mod_then_mod (plh x y) (phl x y + pll_h x y) (pow2 32);
  assert (mul_wide_low x y == ((plh x y + phl x y + pll_h x y) % pow2 32) * pow2 32 + pll_l x y);
  mod_mul (plh x y + phl x y + pll_h x y) (pow2 32) (pow2 32);
  shift_add (plh x y + phl x y + pll_h x y) (pll_l x y);
  assert (mul_wide_low x y == ((plh x y + phl x y + pll_h x y) * pow2 32 + pll_l x y) % pow2 64);
  product_low_expand x y

val product_high32: x: U64.t -> y: U64.t ->
  Lemma ((U64.v x * U64.v y) / pow2 32 == phh x y * pow2 32 + plh x y + phl x y + pll_h x y)
let product_high32 x y =
  Math.pow2_plus 32 32;
  product_expand x y;
  Math.division_addition_lemma (plh x y + phl x y + pll_h x y) (pow2 32) (phh x y * pow2 32);
  mul_div_cancel (phh x y * pow2 32) (pow2 32);
  mul_div_cancel (plh x y + phl x y + pll_h x y) (pow2 32);
  Math.small_division_lemma_1 (pll_l x y) (pow2 32)

val product_high_expand: x: U64.t -> y: U64.t ->
  Lemma ((U64.v x * U64.v y) / pow2 64 == phh x y + (plh x y + phl x y + pll_h x y) / pow2 32)

#set-options "--z3rlimit 20"
let product_high_expand x y =
  Math.pow2_plus 32 32;
  div_product (mul_wide_high x y) (pow2 32) (pow2 32);
  product_high32 x y;
  Math.division_addition_lemma (plh x y + phl x y + pll_h x y) (pow2 32) (phh x y);
  ()
#set-options "--z3rlimit 5"

val mod_spec_multiply: n: nat -> k: pos -> Lemma (((n - n % k) / k) * k == n - n % k)
let mod_spec_multiply n k = Math.lemma_mod_spec2 n k

val mod_spec_mod: n: nat -> k: pos -> Lemma ((n - n % k) % k == 0)
let mod_spec_mod n k =
  assert (n - n % k == (n / k) * k);
  Math.multiple_modulo_lemma (n / k) k

let mul_injective (n: nat) (m: nat) (k: pos) : Lemma (requires (n * k == m * k)) (ensures (n == m)) =
  ()

val div_sum_combine1: n: nat -> m: nat -> k: pos ->
  Lemma ((n / k + m / k) * k == (n - n % k) + (m - m % k))
let div_sum_combine1 n m k =
  Math.distributivity_add_left (n / k) (m / k) k;
  div_mod n k;
  div_mod m k;
  ()

let mod_0 (k: pos) : Lemma (0 % k == 0) = ()

let n_minus_mod_exact (n: nat) (k: pos) : Lemma ((n - n % k) % k == 0) =
  mod_spec_mod n k;
  mod_0 k

let sub_mod_gt_0 (n: nat) (k: pos) : Lemma (0 <= n - n % k) = ()

val sum_rounded_mod_exact: n: nat -> m: nat -> k: pos ->
  Lemma ((((n - n % k) + (m - m % k)) / k) * k == (n - n % k) + (m - m % k))
let sum_rounded_mod_exact n m k =
  n_minus_mod_exact n k;
  n_minus_mod_exact m k;
  sub_mod_gt_0 n k;
  sub_mod_gt_0 m k;
  mod_add (n - n % k) (m - m % k) k;
  Math.div_exact_r ((n - n % k) + (m - m % k)) k

#set-options "--z3rlimit 20"
val div_sum_combine: n: nat -> m: nat -> k: pos ->
  Lemma (n / k + m / k == (n + (m - n % k) - m % k) / k)
let div_sum_combine n m k =
  sum_rounded_mod_exact n m k;
  div_sum_combine1 n m k;
  mul_injective (n / k + m / k) (((n - n % k) + (m - m % k)) / k) k;
  assert (n + m - n % k - m % k == (n - n % k) + (m - m % k))
#set-options "--z3rlimit 5"

val sum_shift_carry: a: nat -> b: nat -> k: pos -> Lemma (a / k + (b + a % k) / k == (a + b) / k)
let sum_shift_carry a b k =
  div_sum_combine a (b + a % k) k;
  //  assert (a / k + (b + a%k) / k == (a + b + (a % k - a % k) - (b + a%k) % k) / k);
  //  assert ((a + b + (a % k - a % k) - (b + a%k) % k) / k == (a + b - (b + a%k) % k) / k);
  add_mod_then_mod b a k;
  Math.lemma_mod_spec (a + b) k

let mul_wide_high_ok (x: U64.t) (y: U64.t)
  : Lemma ((U64.v x * U64.v y) / pow2 64 == mul_wide_high x y) =
  product_high_expand x y;
  sum_shift_carry (phl x y + pll_h x y) (plh x y) (pow2 32)

let product_div_bound (#n: pos) (x: UInt.uint_t n) (y: UInt.uint_t n)
  : Lemma (x * y / pow2 n < pow2 n) =
  Math.pow2_plus n n;
  product_bound x y (pow2 n);
  pow2_div_bound #(n + n) (x * y) n

#set-options "--z3rlimit 100"
let mul_wide (x: U64.t) (y: U64.t)
  : Pure t (requires True) (ensures (fun r -> v r == U64.v x * U64.v y)) =
  mul_wide_low_ok x y;
  mul_wide_high_ok x y;
  product_div_bound (U64.v x) (U64.v y);
  Math.modulo_lemma (mul_wide_high x y) (pow2 64);
  mul_wide_impl x y

