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
module FStar.UInt128

open FStar.Mul

module UInt = FStar.UInt
module Seq = FStar.Seq
module BV = FStar.BitVector

module U32 = FStar.UInt32
module U64 = FStar.UInt64

module Math = FStar.Math.Lemmas

open FStar.BV

(* We try to keep the dependencies of this module low,
by not opening the full Tactics module. This speeds up
checking the library by improving parallelism. *)
module T = FStar.Stubs.Tactics.V2.Builtins
module TD = FStar.Tactics.V2.Derived
module TM = FStar.Tactics.MApply

#set-options "--max_fuel 0 --max_ifuel 0 --split_queries no"
#set-options "--using_facts_from '*,-FStar.Tactics,-FStar.Reflection'"

(* TODO: explain why exactly this is needed? It leads to failures in
HACL* otherwise, claiming that some functions are not Low*. *)
#set-options "--normalize_pure_terms_for_extraction"

[@@ noextract_to "krml"]
noextract
let carry_uint64 (a b: uint_t 64) : Tot (uint_t 64) =
  let ( ^^ ) = UInt.logxor in
  let ( |^ ) = UInt.logor in
  let ( -%^ ) = UInt.sub_mod in
  let ( >>^ ) = UInt.shift_right in
  a ^^ ((a ^^ b) |^ ((a -%^ b) ^^ b)) >>^ 63

[@@ noextract_to "krml"]
noextract
let carry_bv (a b: uint_t 64) =
    bvshr (bvxor (int2bv a)
                 (bvor (bvxor (int2bv a) (int2bv b)) (bvxor (bvsub (int2bv a) (int2bv b)) (int2bv b))))
          63

let carry_uint64_ok (a b:uint_t 64)
  : squash (int2bv (carry_uint64 a b) == carry_bv a b)
  = _ by (T.norm [delta_only [`%carry_uint64]; unascribe];
          let open FStar.Tactics.BV in
          TM.mapply (`FStar.Tactics.BV.Lemmas.trans);
          arith_to_bv_tac ();
          arith_to_bv_tac ();
          T.norm [delta_only [`%carry_bv]];
          TD.trefl())

let fact1 (a b: uint_t 64) = carry_bv a b == int2bv 1
let fact0 (a b: uint_t 64) = carry_bv a b == int2bv 0

let lem_ult_1 (a b: uint_t 64)
  : squash (bvult (int2bv a) (int2bv b) ==> fact1 a b)
  = assert (bvult (int2bv a) (int2bv b) ==> fact1 a b)
       by (T.norm [delta_only [`%fact1;`%carry_bv]];
           T.set_options "--smtencoding.elim_box true --using_facts_from '__Nothing__' --z3smtopt '(set-option :smt.case_split 1)'";
           TD.smt())

let lem_ult_2 (a b:uint_t 64)
  : squash (not (bvult (int2bv a) (int2bv b)) ==> fact0 a b)
  = assert (not (bvult (int2bv a) (int2bv b)) ==> fact0 a b)
       by (T.norm [delta_only [`%fact0;`%carry_bv]];
           T.set_options "--smtencoding.elim_box true --using_facts_from '__Nothing__' --z3smtopt '(set-option :smt.case_split 1)'")

let int2bv_ult (#n: pos) (a b: uint_t n)
  : Lemma (ensures a < b <==> bvult #n (int2bv #n a) (int2bv #n b))
  = introduce (a < b) ==> (bvult #n (int2bv #n a) (int2bv #n b))
    with _ . FStar.BV.int2bv_lemma_ult_1 a b;
    introduce (bvult #n (int2bv #n a) (int2bv #n b)) ==> (a < b)
    with _ . FStar.BV.int2bv_lemma_ult_2 a b

let lem_ult (a b:uint_t 64)
  : Lemma (if a < b
           then fact1 a b
           else fact0 a b)
  = int2bv_ult a b;
    lem_ult_1 a b;
    lem_ult_2 a b

let constant_time_carry (a b: U64.t) : Tot U64.t =
  let open U64 in
  // CONSTANT_TIME_CARRY macro
  // ((a ^ ((a ^ b) | ((a - b) ^ b))) >> (sizeof(a) * 8 - 1))
  // 63 = sizeof(a) * 8 - 1
  a ^^ ((a ^^ b) |^ ((a -%^ b) ^^ b)) >>^ 63ul

let carry_uint64_equiv (a b:UInt64.t)
  : Lemma (U64.v (constant_time_carry a b) == carry_uint64 (U64.v a) (U64.v b))
  = ()

// This type gets a special treatment in KaRaMeL and its definition is never
// printed in the resulting C file.
type uint128: Type0 = { low: U64.t; high: U64.t }

let t = uint128

let _ = intro_ambient n
let _ = intro_ambient t

[@@ noextract_to "krml"]
let v x = U64.v x.low + (U64.v x.high) * (pow2 64)

let div_mod (x:nat) (k:nat{k > 0}) : Lemma (x / k * k + x % k == x) = ()

let uint_to_t x =
    div_mod x (pow2 64);
    { low = U64.uint_to_t (x % (pow2 64));
      high = U64.uint_to_t (x / (pow2 64)); }

let v_inj (x1 x2: t): Lemma (requires (v x1 == v x2))
                            (ensures x1 == x2) =
 assert (uint_to_t (v x1) == uint_to_t (v x2));
 assert (uint_to_t (v x1) == x1);
 assert (uint_to_t (v x2) == x2);
 ()

(* A weird helper used below... seems like the native encoding of
bitvectors may be making these proofs much harder than they should be? *)
let bv2int_fun (#n:pos) (a b : bv_t n)
  : Lemma (requires a == b)
          (ensures bv2int a == bv2int b)
  = ()

(* This proof is quite brittle. It has a bunch of annotations to get
decent verification performance. *)
let constant_time_carry_ok (a b:U64.t)
  : Lemma (constant_time_carry a b ==
           (if U64.lt a b then U64.uint_to_t 1 else U64.uint_to_t 0))
  = calc (==) {
      U64.v (constant_time_carry a b);
    (==) { carry_uint64_equiv a b }
      carry_uint64 (U64.v a) (U64.v b);
    (==) { inverse_num_lemma (carry_uint64 (U64.v a) (U64.v b)) }
      bv2int (int2bv (carry_uint64 (U64.v a) (U64.v b)));
    (==) { carry_uint64_ok (U64.v a) (U64.v b);
           bv2int_fun (int2bv (carry_uint64 (U64.v a) (U64.v b))) (carry_bv (U64.v a) (U64.v b));
           ()
     }
      bv2int (carry_bv (U64.v a) (U64.v b));
    (==) {
           lem_ult (U64.v a) (U64.v b);
           bv2int_fun (carry_bv (U64.v a) (U64.v b)) (if U64.v a < U64.v b then int2bv 1 else int2bv 0)
         }
      bv2int
        (if U64.v a < U64.v b
         then int2bv 1
         else int2bv 0);
    };
    assert (
      bv2int (if U64.v a < U64.v b then int2bv 1 else int2bv 0)
      == U64.v (if U64.lt a b then U64.uint_to_t 1 else U64.uint_to_t 0)) by (T.norm []);
    U64.v_inj (constant_time_carry a b)  (if U64.lt a b then U64.uint_to_t 1 else U64.uint_to_t 0)

let carry (a b: U64.t) : Pure U64.t
  (requires True)
  (ensures (fun r -> U64.v r == (if U64.v a < U64.v b then 1 else 0))) =
  constant_time_carry_ok a b;
  constant_time_carry a b

let carry_sum_ok (a b:U64.t) :
  Lemma (U64.v (carry (U64.add_mod a b) b) == (U64.v a + U64.v b) / (pow2 64)) = ()

let add (a b: t) : Pure t
  (requires (v a + v b < pow2 128))
  (ensures (fun r -> v a + v b = v r)) =
  let l = U64.add_mod a.low b.low in
  carry_sum_ok a.low b.low;
  { low = l;
    high = U64.add (U64.add a.high b.high) (carry l b.low); }

let add_underspec (a b: t) =
    let l = U64.add_mod a.low b.low in
    begin
      if v a + v b < pow2 128
        then carry_sum_ok a.low b.low
        else ()
    end;
    { low = l;
      high = U64.add_underspec (U64.add_underspec a.high b.high) (carry l b.low); }

val mod_mod: a:nat -> k:nat{k>0} -> k':nat{k'>0} ->
    Lemma ((a % k) % (k'*k) == a % k)
let mod_mod a k k' =
  assert (a % k < k);
  assert (a % k < k' * k)

let mod_spec (a:nat) (k:nat{k > 0}) :
  Lemma (a % k == a - a / k * k) = ()

val div_product : n:nat -> m1:nat{m1>0} -> m2:nat{m2>0} ->
  Lemma (n / (m1*m2) == (n / m1) / m2)
let div_product n m1 m2 =
  Math.division_multiplication_lemma n m1 m2

val mul_div_cancel : n:nat -> k:nat{k>0} ->
  Lemma ((n * k) / k == n)
let mul_div_cancel n k =
  Math.cancel_mul_div n k

val mod_mul: n:nat -> k1:pos -> k2:pos ->
  Lemma ((n % k2) * k1 == (n * k1) % (k1*k2))
let mod_mul n k1 k2 =
  Math.modulo_scale_lemma n k1 k2

let mod_spec_rew_n (n:nat) (k:nat{k > 0}) :
  Lemma (n == n / k * k + n % k) = mod_spec n k

val mod_add: n1:nat -> n2:nat -> k:nat{k > 0} ->
  Lemma ((n1 % k + n2 % k) % k == (n1 + n2) % k)
let mod_add n1 n2 k = Math.modulo_distributivity n1 n2 k

val mod_add_small: n1:nat -> n2:nat -> k:nat{k > 0} -> Lemma
  (requires (n1 % k + n2 % k < k))
  (ensures (n1 % k + n2 % k == (n1 + n2) % k))
let mod_add_small n1 n2 k =
  mod_add n1 n2 k;
  Math.small_modulo_lemma_1 (n1%k + n2%k) k

// This proof is pretty stable with the calc proof, but it can fail
// ~1% of the times, so add a retry.
#push-options "--split_queries no --z3rlimit 20 --retry 5"
let add_mod (a b: t) : Pure t
  (requires True)
  (ensures (fun r -> (v a + v b) % pow2 128 = v r)) =

  let l = U64.add_mod a.low b.low in
  let r = { low = l;
            high = U64.add_mod (U64.add_mod a.high b.high) (carry l b.low)} in
  let a_l = U64.v a.low in
  let a_h = U64.v a.high in
  let b_l = U64.v b.low in
  let b_h = U64.v b.high in
  carry_sum_ok a.low b.low;
  Math.lemma_mod_plus_distr_l (a_h + b_h) ((a_l + b_l) / (pow2 64)) (pow2 64);
  calc (==) {
    U64.v r.high * pow2 64;
    == {}
    ((a_h + b_h + (a_l + b_l) / (pow2 64)) % pow2 64) * pow2 64;
    == { mod_mul (a_h + b_h + (a_l + b_l) / (pow2 64)) (pow2 64) (pow2 64) }
    ((a_h + b_h + (a_l + b_l) / (pow2 64)) * pow2 64) % (pow2 64 * pow2 64);
    == {}
    ((a_h + b_h + (a_l + b_l)/(pow2 64)) * pow2 64)
      % pow2 128;
    == {}
    (a_h * pow2 64 + b_h * pow2 64 + ((a_l + b_l)/(pow2 64)) * pow2 64)
      % pow2 128;
  };
  assert (U64.v r.low == (U64.v r.low) % pow2 128);
  mod_add_small (a_h * pow2 64 +
                  b_h * pow2 64 +
                  (a_l + b_l) / (pow2 64) * (pow2 64))
          ((a_l + b_l) % (pow2 64))
          (pow2 128);
  assert (U64.v r.low + U64.v r.high * pow2 64 ==
                (a_h * pow2 64 +
                b_h * pow2 64 +
                (a_l + b_l) / (pow2 64) * (pow2 64) + (a_l + b_l) % (pow2 64)) % pow2 128);
  mod_spec_rew_n (a_l + b_l) (pow2 64);
  assert (v r ==
          (a_h * pow2 64 +
          b_h * pow2 64 +
          a_l + b_l) % pow2 128);
  assert_spinoff ((v a + v b) % pow2 128 = v r);
  r
#pop-options

#push-options "--retry 5"
let sub (a b: t) : Pure t
  (requires (v a - v b >= 0))
  (ensures (fun r -> v r = v a - v b)) =
  let l = U64.sub_mod a.low b.low in
  { low = l;
    high = U64.sub (U64.sub a.high b.high) (carry a.low l); }
#pop-options

let sub_underspec (a b: t) =
  let l = U64.sub_mod a.low b.low in
  { low = l;
    high = U64.sub_underspec (U64.sub_underspec a.high b.high) (carry a.low l); }

let sub_mod_impl (a b: t) : t =
  let l = U64.sub_mod a.low b.low in
  { low = l;
    high = U64.sub_mod (U64.sub_mod a.high b.high) (carry a.low l); }

#push-options "--retry 10" // flaky
let sub_mod_pos_ok (a b:t) : Lemma
  (requires (v a - v b >= 0))
  (ensures (v (sub_mod_impl a b) = v a - v b)) =
  assert (sub a b == sub_mod_impl a b);
  ()
#pop-options

val u64_diff_wrap : a:U64.t -> b:U64.t ->
  Lemma  (requires (U64.v a < U64.v b))
         (ensures (U64.v (U64.sub_mod a b) == U64.v a - U64.v b + pow2 64))
let u64_diff_wrap a b = ()

#push-options "--z3rlimit 20"
val sub_mod_wrap1_ok : a:t -> b:t -> Lemma
  (requires (v a - v b < 0 /\ U64.v a.low < U64.v b.low))
  (ensures (v (sub_mod_impl a b) = v a - v b + pow2 128))

#push-options "--retry 10"
let sub_mod_wrap1_ok a b =
    // carry == 1 and subtraction in low wraps
    let l = U64.sub_mod a.low b.low in
    assert (U64.v (carry a.low l) == 1);
    u64_diff_wrap a.low b.low;
    // a.high <= b.high since v a < v b;
    // case split on equality and strictly less
    if U64.v a.high = U64.v b.high then ()
    else begin
      u64_diff_wrap a.high b.high;
      ()
    end
#pop-options
#pop-options


let sum_lt (a1 a2 b1 b2:nat) : Lemma
  (requires (a1 + a2 < b1 + b2 /\ a1 >= b1))
  (ensures (a2 < b2)) = ()

let sub_mod_wrap2_ok (a b:t) : Lemma
  (requires (v a - v b < 0 /\ U64.v a.low >= U64.v b.low))
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

let sub_mod_wrap_ok (a b:t) : Lemma
  (requires (v a - v b < 0))
  (ensures (v (sub_mod_impl a b) = v a - v b + pow2 128)) =
  if U64.v a.low < U64.v b.low
    then sub_mod_wrap1_ok a b
    else sub_mod_wrap2_ok a b

#restart-solver
#push-options "--z3rlimit 40"
let sub_mod (a b: t) : Pure t
  (requires True)
  (ensures (fun r -> v r = (v a - v b) % pow2 128)) =
  (if v a - v b >= 0
    then sub_mod_pos_ok a b
    else sub_mod_wrap_ok a b);
  sub_mod_impl a b
#pop-options

#restart-solver

val shift_bound : #n:nat -> num:UInt.uint_t n -> n':nat ->
  Lemma (num * pow2 n' <= pow2 (n'+n) - pow2 n')
let shift_bound #n num n' =
  Math.lemma_mult_le_right (pow2 n') num (pow2 n - 1);
  Math.distributivity_sub_left (pow2 n) 1 (pow2 n');
  Math.pow2_plus n' n

val append_uint : #n1:nat -> #n2:nat -> num1:UInt.uint_t n1 -> num2:UInt.uint_t n2 -> UInt.uint_t (n1+n2)
let append_uint #n1 #n2 num1 num2 =
  shift_bound num2 n1;
  num1 + num2 * pow2 n1

val to_vec_append : #n1:nat{n1 > 0} -> #n2:nat{n2 > 0} -> num1:UInt.uint_t n1 -> num2:UInt.uint_t n2 ->
  Lemma (UInt.to_vec (append_uint num1 num2) == Seq.append (UInt.to_vec num2) (UInt.to_vec num1))
let to_vec_append #n1 #n2 num1 num2 =
  UInt.append_lemma (UInt.to_vec num2) (UInt.to_vec num1)

let vec128 (a: t) : BV.bv_t 128 = UInt.to_vec #128 (v a)
let vec64 (a: U64.t) : BV.bv_t 64 = UInt.to_vec (U64.v a)

let to_vec_v (a: t) :
  Lemma (vec128 a == Seq.append (vec64 a.high) (vec64 a.low)) =
  to_vec_append (U64.v a.low) (U64.v a.high)

val logand_vec_append (#n1 #n2: pos) (a1 b1: BV.bv_t n1) (a2 b2: BV.bv_t n2) :
  Lemma (Seq.append (BV.logand_vec a1 b1) (BV.logand_vec a2 b2) ==
         BV.logand_vec #(n1 + n2) (Seq.append a1 a2) (Seq.append b1 b2))
let logand_vec_append #n1 #n2 a1 b1 a2 b2 =
  Seq.lemma_eq_intro (Seq.append (BV.logand_vec a1 b1) (BV.logand_vec a2 b2))
                     (BV.logand_vec #(n1 + n2) (Seq.append a1 a2) (Seq.append b1 b2))

let logand (a b: t) : Pure t
  (requires True)
  (ensures (fun r -> v r = UInt.logand #128 (v a) (v b))) =
  let r = { low = U64.logand a.low b.low;
            high = U64.logand a.high b.high } in
  to_vec_v r;
  assert (vec128 r == Seq.append (vec64 r.high) (vec64 r.low));
  logand_vec_append (vec64 a.high) (vec64 b.high)
                    (vec64 a.low) (vec64 b.low);
  to_vec_v a;
  to_vec_v b;
  assert (vec128 r == BV.logand_vec (vec128 a) (vec128 b));
  r

val logxor_vec_append (#n1 #n2: pos) (a1 b1: BV.bv_t n1) (a2 b2: BV.bv_t n2) :
  Lemma (Seq.append (BV.logxor_vec a1 b1) (BV.logxor_vec a2 b2) ==
         BV.logxor_vec #(n1 + n2) (Seq.append a1 a2) (Seq.append b1 b2))
let logxor_vec_append #n1 #n2 a1 b1 a2 b2 =
  Seq.lemma_eq_intro (Seq.append (BV.logxor_vec a1 b1) (BV.logxor_vec a2 b2))
                     (BV.logxor_vec #(n1 + n2) (Seq.append a1 a2) (Seq.append b1 b2))

let logxor (a b: t) : Pure t
  (requires True)
  (ensures (fun r -> v r = UInt.logxor #128 (v a) (v b))) =
  let r = { low = U64.logxor a.low b.low;
  high = U64.logxor a.high b.high } in
  to_vec_v r;
  assert (vec128 r == Seq.append (vec64 r.high) (vec64 r.low));
  logxor_vec_append (vec64 a.high) (vec64 b.high)
  (vec64 a.low) (vec64 b.low);
  to_vec_v a;
  to_vec_v b;
  assert (vec128 r == BV.logxor_vec (vec128 a) (vec128 b));
  r

val logor_vec_append (#n1 #n2: pos) (a1 b1: BV.bv_t n1) (a2 b2: BV.bv_t n2) :
  Lemma (Seq.append (BV.logor_vec a1 b1) (BV.logor_vec a2 b2) ==
        BV.logor_vec #(n1 + n2) (Seq.append a1 a2) (Seq.append b1 b2))
let logor_vec_append #n1 #n2 a1 b1 a2 b2 =
  Seq.lemma_eq_intro (Seq.append (BV.logor_vec a1 b1) (BV.logor_vec a2 b2))
                     (BV.logor_vec #(n1 + n2) (Seq.append a1 a2) (Seq.append b1 b2))

let logor (a b: t) : Pure t
  (requires True)
  (ensures (fun r -> v r = UInt.logor #128 (v a) (v b))) =
  let r = { low = U64.logor a.low b.low;
            high = U64.logor a.high b.high } in
  to_vec_v r;
  assert (vec128 r == Seq.append (vec64 r.high) (vec64 r.low));
  logor_vec_append (vec64 a.high) (vec64 b.high)
                   (vec64 a.low) (vec64 b.low);
  to_vec_v a;
  to_vec_v b;
  assert (vec128 r == BV.logor_vec (vec128 a) (vec128 b));
  r

val lognot_vec_append (#n1 #n2: pos) (a1: BV.bv_t n1) (a2: BV.bv_t n2) :
  Lemma (Seq.append (BV.lognot_vec a1) (BV.lognot_vec a2) ==
        BV.lognot_vec #(n1 + n2) (Seq.append a1 a2))
let lognot_vec_append #n1 #n2 a1 a2 =
  Seq.lemma_eq_intro (Seq.append (BV.lognot_vec a1) (BV.lognot_vec a2))
                      (BV.lognot_vec #(n1 + n2) (Seq.append a1 a2))

let lognot (a: t) : Pure t
  (requires True)
  (ensures (fun r -> v r = UInt.lognot #128 (v a))) =
  let r = { low = U64.lognot a.low;
            high = U64.lognot a.high } in
  to_vec_v r;
  assert (vec128 r == Seq.append (vec64 r.high) (vec64 r.low));
  lognot_vec_append (vec64 a.high) (vec64 a.low);
  to_vec_v a;
  assert (vec128 r == BV.lognot_vec (vec128 a));
  r

let mod_mul_cancel (n:nat) (k:nat{k > 0}) :
  Lemma ((n * k) % k == 0) =
  mod_spec (n * k) k;
  mul_div_cancel n k;
  ()

let shift_past_mod (n:nat) (k1:nat) (k2:nat{k2 >= k1}) :
  Lemma ((n * pow2 k2) % pow2 k1 == 0) =
  assert (k2 == (k2 - k1) + k1);
  Math.pow2_plus (k2 - k1) k1;
  Math.paren_mul_right n (pow2 (k2 - k1)) (pow2 k1);
  mod_mul_cancel (n * pow2 (k2 - k1)) (pow2 k1)

val mod_double: a:nat -> k:nat{k>0} ->
    Lemma (a % k % k == a % k)
let mod_double a k =
  mod_mod a k 1

let shift_left_large_val (#n1:nat) (#n2: nat) (a1:UInt.uint_t n1) (a2:UInt.uint_t n2) (s:nat) :
  Lemma ((a1 + a2 * pow2 n1) * pow2 s == (a1 * pow2 s + a2 * pow2 (n1+s))) =
  Math.distributivity_add_left a1 (a2 * pow2 n1) (pow2 s);
  Math.paren_mul_right a2 (pow2 n1) (pow2 s);
  Math.pow2_plus n1 s

#push-options "--z3rlimit 40"
let shift_left_large_lemma (#n1: nat) (#n2: nat) (a1:UInt.uint_t n1) (a2:UInt.uint_t n2) (s: nat{s >= n2}) :
  Lemma (((a1 + a2 * pow2 n1) * pow2 s) % pow2 (n1+n2) ==
         (a1 * pow2 s) % pow2 (n1+n2)) =
  shift_left_large_val a1 a2 s;
  mod_add (a1 * pow2 s) (a2 * pow2 (n1+s)) (pow2 (n1+n2));
  shift_past_mod a2 (n1+n2) (n1+s);
  mod_double (a1 * pow2 s) (pow2 (n1+n2));
  ()
#pop-options

val shift_left_large_lemma_t : a:t -> s:nat ->
  Lemma (requires (s >= 64))
        (ensures ((v a * pow2 s) % pow2 128 ==
                  (U64.v a.low * pow2 s) % pow2 128))
let shift_left_large_lemma_t a s =
  shift_left_large_lemma #64 #64 (U64.v a.low) (U64.v a.high) s

private let u32_64: n:U32.t{U32.v n == 64} = U32.uint_to_t 64

val div_pow2_diff: a:nat -> n1:nat -> n2:nat{n2 <= n1} -> Lemma
  (requires True)
  (ensures (a / pow2 (n1 - n2) == a * pow2 n2 / pow2 n1))
let div_pow2_diff a n1 n2 =
  Math.pow2_plus n2 (n1-n2);
  assert (a * pow2 n2 / pow2 n1 == a * pow2 n2 / (pow2 n2 * pow2 (n1 - n2)));
  div_product (a * pow2 n2) (pow2 n2) (pow2 (n1-n2));
  mul_div_cancel a (pow2 n2)

val mod_mul_pow2 : n:nat -> e1:nat -> e2:nat ->
  Lemma (n % pow2 e1 * pow2 e2 <= pow2 (e1+e2) - pow2 e2)
let mod_mul_pow2 n e1 e2 =
  Math.lemma_mod_lt n (pow2 e1);
  Math.lemma_mult_le_right (pow2 e2) (n % pow2 e1) (pow2 e1 - 1);
  assert (n % pow2 e1 * pow2 e2 <= pow2 e1 * pow2 e2 - pow2 e2);
  Math.pow2_plus e1 e2

let pow2_div_bound #b (n:UInt.uint_t b) (s:nat{s <= b}) :
  Lemma (n / pow2 s < pow2 (b - s)) =
  Math.lemma_div_lt n b s

#push-options "--smtencoding.l_arith_repr native --z3rlimit 40"
let add_u64_shift_left (hi lo: U64.t) (s: U32.t{U32.v s < 64}) : Pure U64.t
  (requires (U32.v s <> 0))
  (ensures (fun r -> U64.v r = (U64.v hi * pow2 (U32.v s)) % pow2 64 + U64.v lo / pow2 (64 - U32.v s))) =
  let high = U64.shift_left hi s in
  let low = U64.shift_right lo (U32.sub u32_64 s) in
  let s = U32.v s in
  let high_n = U64.v hi % pow2 (64 - s) * pow2 s in
  let low_n = U64.v lo / pow2 (64 - s) in
  Math.pow2_plus (64-s) s;
  mod_mul (U64.v hi) (pow2 s) (pow2 (64-s));
  assert (U64.v high == high_n);
  assert (U64.v low == low_n);
  pow2_div_bound (U64.v lo) (64-s);
  assert (low_n < pow2 s);
  mod_mul_pow2 (U64.v hi) (64 - s) s;
  U64.add high low
#pop-options


let div_plus_multiple (a:nat) (b:nat) (k:pos) :
  Lemma (requires (a < k))
        (ensures ((a + b * k) / k == b)) =
  Math.division_addition_lemma a k b;
  Math.small_division_lemma_1 a k

val div_add_small: n:nat -> m:nat -> k1:pos -> k2:pos ->
  Lemma (requires (n < k1))
        (ensures (k1*m / (k1*k2) == (n + k1*m) / (k1*k2)))
let div_add_small n m k1 k2 =
  div_product (k1*m) k1 k2;
  div_product (n+k1*m) k1 k2;
  mul_div_cancel m k1;
  assert (k1*m/k1 == m);
  div_plus_multiple n m k1

val add_mod_small: n: nat -> m:nat -> k1:pos -> k2:pos ->
  Lemma (requires (n < k1))
        (ensures (n + (k1 * m) % (k1 * k2) ==
                  (n + k1 * m) % (k1 * k2)))
let add_mod_small n m k1 k2 =
  mod_spec (k1 * m) (k1 * k2);
  mod_spec (n + k1 * m) (k1 * k2);
  div_add_small n m k1 k2

let mod_then_mul_64 (n:nat) : Lemma (n % pow2 64 * pow2 64 == n * pow2 64 % pow2 128) =
  Math.pow2_plus 64 64;
  mod_mul n (pow2 64) (pow2 64)

let mul_abc_to_acb (a b c: int) : Lemma (a * b * c == a * c * b) = ()

let add_u64_shift_left_respec (hi lo:U64.t) (s:U32.t{U32.v s < 64}) : Pure U64.t
  (requires (U32.v s <> 0))
  (ensures (fun r ->
              U64.v r * pow2 64 ==
              (U64.v hi * pow2 64) * pow2 (U32.v s) % pow2 128 +
              U64.v lo * pow2 (U32.v s) / pow2 64 * pow2 64)) =
  let r = add_u64_shift_left hi lo s in
  let hi = U64.v hi in
  let lo = U64.v lo in
  let s = U32.v s in
  // spec of add_u64_shift_left
  assert (U64.v r == hi * pow2 s % pow2 64 + lo / pow2 (64 - s));
  Math.distributivity_add_left (hi * pow2 s % pow2 64) (lo / pow2 (64-s)) (pow2 64);
  mod_then_mul_64 (hi * pow2 s);
  assert (hi * pow2 s % pow2 64 * pow2 64 == (hi * pow2 s * pow2 64) % pow2 128);
  div_pow2_diff lo 64 s;
  assert (lo / pow2 (64-s) == lo * pow2 s / pow2 64);
  assert (U64.v r * pow2 64 == hi * pow2 s * pow2 64 % pow2 128 + lo * pow2 s / pow2 64 * pow2 64);
  mul_abc_to_acb hi (pow2 s) (pow2 64);
  r

val add_mod_small' : n:nat -> m:nat -> k:pos ->
  Lemma (requires (n + m % k < k))
        (ensures (n + m % k == (n + m) % k))
let add_mod_small' n m k =
  Math.lemma_mod_lt (n + m % k) k;
  Math.modulo_lemma n k;
  mod_add n m k

#push-options "--retry 5"
let shift_t_val (a: t) (s: nat) :
    Lemma (v a * pow2 s == U64.v a.low * pow2 s + U64.v a.high * pow2 (64+s)) =
    Math.pow2_plus 64 s;
    ()
#pop-options

val mul_mod_bound : n:nat -> s1:nat -> s2:nat{s2>=s1} ->
  Lemma (n * pow2 s1 % pow2 s2 <= pow2 s2 - pow2 s1)

#push-options "--retry 5"
let mul_mod_bound n s1 s2 =
  // n * pow2 s1 % pow2 s2 == n % pow2 (s2-s1) * pow2 s1
  // n % pow2 (s2-s1) <= pow2 (s2-s1) - 1
  // n % pow2 (s2-s1) * pow2 s1 <= pow2 s2 - pow2 s1
  mod_mul n (pow2 s1) (pow2 (s2-s1));
  // assert (n * pow2 s1 % pow2 s2 == n % pow2 (s2-s1) * pow2 s1);
  Math.lemma_mod_lt n (pow2 (s2-s1));
  Math.lemma_mult_le_right (pow2 s1) (n % pow2 (s2-s1)) (pow2 (s2-s1) - 1);
  Math.pow2_plus (s2-s1) s1
#pop-options

let add_lt_le (a a' b b': int) :
  Lemma (requires (a < a' /\ b <= b'))
  (ensures (a + b < a' + b')) = ()

let u64_pow2_bound (a: UInt.uint_t 64) (s: nat) :
  Lemma (a * pow2 s < pow2 (64+s)) =
  Math.pow2_plus 64 s;
  Math.lemma_mult_le_right (pow2 s) a (pow2 64)

let shift_t_mod_val' (a: t) (s: nat{s < 64}) :
  Lemma ((v a * pow2 s) % pow2 128 ==
        U64.v a.low * pow2 s + U64.v a.high * pow2 (64+s) % pow2 128) =
  let a_l = U64.v a.low in
  let a_h = U64.v a.high in
  u64_pow2_bound a_l s;
  mul_mod_bound a_h (64+s) 128;
  // assert (a_h * pow2 (64+s) % pow2 128 <= pow2 128 - pow2 (64+s));
  add_lt_le (a_l * pow2 s) (pow2 (64+s)) (a_h * pow2 (64+s) % pow2 128) (pow2 128 - pow2 (64+s));
  add_mod_small' (a_l * pow2 s) (a_h * pow2 (64+s)) (pow2 128);
  shift_t_val a s;
  ()

let shift_t_mod_val (a: t) (s: nat{s < 64}) :
  Lemma ((v a * pow2 s) % pow2 128 ==
        U64.v a.low * pow2 s + (U64.v a.high * pow2 64) * pow2 s % pow2 128) =
  let a_l = U64.v a.low in
  let a_h = U64.v a.high in
  shift_t_mod_val' a s;
  Math.pow2_plus 64 s;
  Math.paren_mul_right a_h (pow2 64) (pow2 s);
  ()

#push-options "--z3rlimit 20"
let shift_left_small (a: t) (s: U32.t) : Pure t
  (requires (U32.v s < 64))
  (ensures (fun r -> v r = (v a * pow2 (U32.v s)) % pow2 128)) =
  if U32.eq s 0ul then a
  else
    let r = { low = U64.shift_left a.low s;
              high = add_u64_shift_left_respec a.high a.low s; } in
    let s = U32.v s in
    let a_l = U64.v a.low in
    let a_h = U64.v a.high in
    mod_spec_rew_n (a_l * pow2 s) (pow2 64);
    shift_t_mod_val a s;
    r
#pop-options

val shift_left_large : a:t -> s:U32.t{U32.v s >= 64 /\ U32.v s < 128} ->
  r:t{v r = (v a * pow2 (U32.v s)) % pow2 128}

#push-options "--z3rlimit 50 --retry 5" // sporadically fails
let shift_left_large a s =
  let h_shift = U32.sub s u32_64 in
  assert (U32.v h_shift < 64);
  let r = { low = U64.uint_to_t 0;
            high = U64.shift_left a.low h_shift; } in
  assert (U64.v r.high == (U64.v a.low * pow2 (U32.v s - 64)) % pow2 64);
  mod_mul (U64.v a.low * pow2 (U32.v s - 64)) (pow2 64) (pow2 64);
  Math.pow2_plus (U32.v s - 64) 64;
  assert (U64.v r.high * pow2 64 == (U64.v a.low * pow2 (U32.v s)) % pow2 128);
  shift_left_large_lemma_t a (U32.v s);
  r
#pop-options

let shift_left a s =
  if (U32.lt s u32_64) then shift_left_small a s
  else shift_left_large a s

#restart-solver
let add_u64_shift_right (hi lo: U64.t) (s: U32.t{U32.v s < 64}) : Pure U64.t
  (requires (U32.v s <> 0))
  (ensures (fun r -> U64.v r == U64.v lo / pow2 (U32.v s) +
                             U64.v hi * pow2 (64 - U32.v s) % pow2 64)) =
  let low = U64.shift_right lo s in
  let high = U64.shift_left hi (U32.sub u32_64 s) in
  let s = U32.v s in
  let low_n = U64.v lo / pow2 s in
  let high_n = U64.v hi % pow2 s * pow2 (64 - s) in
  Math.pow2_plus (64-s) s;
  mod_mul (U64.v hi) (pow2 (64-s)) (pow2 s);
  assert (U64.v high == high_n);
  pow2_div_bound (U64.v lo) s;
  assert (low_n < pow2 (64 - s));
  mod_mul_pow2 (U64.v hi) s (64 - s);
  U64.add low high

val mul_pow2_diff: a:nat -> n1:nat -> n2:nat{n2 <= n1} ->
  Lemma (a * pow2 (n1 - n2) == a * pow2 n1 / pow2 n2)
let mul_pow2_diff a n1 n2 =
  Math.paren_mul_right a (pow2 (n1-n2)) (pow2 n2);
  mul_div_cancel (a * pow2 (n1 - n2)) (pow2 n2);
  Math.pow2_plus (n1 - n2) n2

#restart-solver
let add_u64_shift_right_respec (hi lo:U64.t) (s: U32.t{U32.v s < 64}) : Pure U64.t
  (requires (U32.v s <> 0))
  (ensures (fun r -> U64.v r == U64.v lo / pow2 (U32.v s) +
                             U64.v hi * pow2 64 / pow2 (U32.v s) % pow2 64)) =
  let r = add_u64_shift_right hi lo s in
  let s = U32.v s in
  mul_pow2_diff (U64.v hi) 64 s;
  r

#restart-solver
let mul_div_spec (n:nat) (k:pos) : Lemma (n / k * k == n - n % k) = ()

let mul_distr_sub (n1 n2:nat) (k:nat) : Lemma ((n1 - n2) * k == n1 * k - n2 * k) = ()

val div_product_comm : n1:nat -> k1:pos -> k2:pos ->
    Lemma (n1 / k1 / k2 == n1 / k2 / k1)
let div_product_comm n1 k1 k2 =
    div_product n1 k1 k2;
    div_product n1 k2 k1

val shift_right_reconstruct : a_h:UInt.uint_t 64 -> s:nat{s < 64} ->
  Lemma (a_h * pow2 (64-s) == a_h / pow2 s * pow2 64 + a_h * pow2 64 / pow2 s % pow2 64)
let shift_right_reconstruct a_h s =
  mul_pow2_diff a_h 64 s;
  mod_spec_rew_n (a_h * pow2 (64-s)) (pow2 64);
  div_product_comm (a_h * pow2 64) (pow2 s) (pow2 64);
  mul_div_cancel a_h (pow2 64);
  assert (a_h / pow2 s * pow2 64 == a_h * pow2 64 / pow2 s / pow2 64 * pow2 64);
  ()

val u128_div_pow2 (a: t) (s:nat{s < 64}) :
  Lemma (v a / pow2 s == U64.v a.low / pow2 s + U64.v a.high * pow2 (64 - s))
let u128_div_pow2 a s =
  Math.pow2_plus (64-s) s;
  Math.paren_mul_right (U64.v a.high) (pow2 (64-s)) (pow2 s);
  Math.division_addition_lemma (U64.v a.low) (pow2 s) (U64.v a.high * pow2 (64 - s))

#restart-solver
let shift_right_small (a: t) (s: U32.t{U32.v s < 64}) : Pure t
  (requires True)
  (ensures (fun r -> v r == v a / pow2 (U32.v s))) =
  if U32.eq s 0ul then a
  else
  let r = { low = add_u64_shift_right_respec a.high a.low s;
            high = U64.shift_right a.high s; } in
  let a_h = U64.v a.high in
  let a_l = U64.v a.low in
  let s = U32.v s in
  shift_right_reconstruct a_h s;
  assert (v r == a_h * pow2 (64-s) + a_l / pow2 s);
  u128_div_pow2 a s;
  r

let shift_right_large (a: t) (s: U32.t{U32.v s >= 64 /\ U32.v s < 128}) : Pure t
  (requires True)
  (ensures (fun r -> v r == v a / pow2 (U32.v s))) =
  let r = { high = U64.uint_to_t 0;
            low = U64.shift_right a.high (U32.sub s u32_64); } in
  let s = U32.v s in
  Math.pow2_plus 64 (s - 64);
  div_product (v a) (pow2 64) (pow2 (s - 64));
  assert (v a / pow2 s == v a / pow2 64 / pow2 (s - 64));
  div_plus_multiple (U64.v a.low) (U64.v a.high) (pow2 64);
  r

let shift_right (a: t) (s: U32.t) : Pure t
  (requires (U32.v s < 128))
  (ensures (fun r -> v r == v a / pow2 (U32.v s))) =
  if U32.lt s u32_64
    then shift_right_small a s
    else shift_right_large a s

let eq (a b:t) = U64.eq a.low b.low && U64.eq a.high b.high
let gt (a b:t) = U64.gt a.high b.high ||
                 (U64.eq a.high b.high && U64.gt a.low b.low)
let lt (a b:t) = U64.lt a.high b.high ||
                 (U64.eq a.high b.high && U64.lt a.low b.low)
let gte (a b:t) = U64.gt a.high b.high ||
                  (U64.eq a.high b.high && U64.gte a.low b.low)
let lte (a b:t) = U64.lt a.high b.high ||
                  (U64.eq a.high b.high && U64.lte a.low b.low)

let u64_logand_comm (a b:U64.t) : Lemma (U64.logand a b == U64.logand b a) =
  UInt.logand_commutative (U64.v a) (U64.v b)

val u64_and_0 (a b:U64.t) :
  Lemma (U64.v b = 0 ==> U64.v (U64.logand a b) = 0)
  [SMTPat (U64.logand a b)]
let u64_and_0 a b = UInt.logand_lemma_1 (U64.v a)

let u64_0_and (a b:U64.t) :
  Lemma (U64.v a = 0 ==> U64.v (U64.logand a b) = 0)
  [SMTPat (U64.logand a b)] =
  u64_logand_comm a b

val u64_1s_and (a b:U64.t) :
  Lemma (U64.v a = pow2 64 - 1 /\
         U64.v b = pow2 64 - 1 ==> U64.v (U64.logand a b) = pow2 64 - 1)
  [SMTPat (U64.logand a b)]
let u64_1s_and a b = UInt.logand_lemma_2 (U64.v a)

let eq_mask (a b: t) : Pure t
  (requires True)
  (ensures (fun r -> (v a = v b ==> v r = pow2 128 - 1) /\ (v a <> v b ==> v r = 0))) =
  let mask = U64.logand (U64.eq_mask a.low b.low)
                        (U64.eq_mask a.high b.high) in
  { low = mask; high = mask; }

private let gte_characterization (a b: t) :
  Lemma (v a >= v b ==>
        U64.v a.high > U64.v b.high \/
        (U64.v a.high = U64.v b.high /\ U64.v a.low >= U64.v b.low)) = ()

private let lt_characterization (a b: t) :
  Lemma (v a < v b ==>
         U64.v a.high < U64.v b.high \/
         (U64.v a.high = U64.v b.high /\ U64.v a.low < U64.v b.low)) = ()

let u64_logor_comm (a b:U64.t) : Lemma (U64.logor a b == U64.logor b a) =
  UInt.logor_commutative (U64.v a) (U64.v b)

val u64_or_1 (a b:U64.t) :
  Lemma (U64.v b = pow2 64 - 1 ==> U64.v (U64.logor a b) = pow2 64 - 1)
  [SMTPat (U64.logor a b)]
let u64_or_1 a b = UInt.logor_lemma_2 (U64.v a)

let u64_1_or (a b:U64.t) :
  Lemma (U64.v a = pow2 64 - 1 ==> U64.v (U64.logor a b) = pow2 64 - 1)
  [SMTPat (U64.logor a b)] =
  u64_logor_comm a b

val u64_or_0 (a b:U64.t) :
  Lemma (U64.v a = 0 /\ U64.v b = 0 ==> U64.v (U64.logor a b) = 0)
  [SMTPat (U64.logor a b)]
let u64_or_0 a b = UInt.logor_lemma_1 (U64.v a)

val u64_not_0 (a:U64.t) :
  Lemma (U64.v a = 0 ==> U64.v (U64.lognot a) = pow2 64 - 1)
  [SMTPat (U64.lognot a)]
let u64_not_0 a = UInt.lognot_lemma_1 #64

val u64_not_1 (a:U64.t) :
  Lemma (U64.v a = pow2 64 - 1 ==> U64.v (U64.lognot a) = 0)
  [SMTPat (U64.lognot a)]
let u64_not_1 a =
  UInt.nth_lemma (UInt.lognot #64 (UInt.ones 64)) (UInt.zero 64)

let gte_mask (a b: t) : Pure t
  (requires True)
  (ensures (fun r -> (v a >= v b ==> v r = pow2 128 - 1) /\ (v a < v b ==> v r = 0))) =
  let mask_hi_gte = U64.logand (U64.gte_mask a.high b.high)
                               (U64.lognot (U64.eq_mask a.high b.high)) in
  let mask_lo_gte = U64.logand (U64.eq_mask a.high b.high)
                               (U64.gte_mask a.low b.low) in
  let mask = U64.logor mask_hi_gte mask_lo_gte in
  gte_characterization a b;
  lt_characterization a b;
  { low = mask; high = mask; }

let uint64_to_uint128 (a:U64.t) = { low = a; high = U64.uint_to_t 0; }

let uint128_to_uint64 (a:t) : b:U64.t{U64.v b == v a % pow2 64} = a.low

inline_for_extraction
let u64_l32_mask: x:U64.t{U64.v x == pow2 32 - 1} = U64.uint_to_t 0xffffffff

let u64_mod_32 (a: U64.t) : Pure U64.t
  (requires True)
  (ensures (fun r -> U64.v r = U64.v a % pow2 32)) =
  UInt.logand_mask (U64.v a) 32;
  U64.logand a u64_l32_mask

let u64_32_digits (a: U64.t) : Lemma (U64.v a / pow2 32 * pow2 32 + U64.v a % pow2 32 == U64.v a) =
  div_mod (U64.v a) (pow2 32)

val mul32_digits : x:UInt.uint_t 64 -> y:UInt.uint_t 32 ->
  Lemma (x * y == (x / pow2 32 * y) * pow2 32 + (x % pow2 32) * y)
let mul32_digits x y = ()

let u32_32 : x:U32.t{U32.v x == 32} = U32.uint_to_t 32

#push-options "--z3rlimit 30"
let u32_combine (hi lo: U64.t) : Pure U64.t
  (requires (U64.v lo < pow2 32))
  (ensures (fun r -> U64.v r = U64.v hi % pow2 32 * pow2 32 + U64.v lo)) =
  U64.add lo (U64.shift_left hi u32_32)
#pop-options

let product_bound (a b:nat) (k:pos) :
  Lemma (requires (a < k /\ b < k))
        (ensures a * b <= k * k - 2*k + 1) =
  Math.lemma_mult_le_right b a (k-1);
  Math.lemma_mult_le_left (k-1) b (k-1)

val uint_product_bound : #n:nat -> a:UInt.uint_t n -> b:UInt.uint_t n ->
  Lemma (a * b <= pow2 (2*n) - 2*(pow2 n) + 1)
let uint_product_bound #n a b =
  product_bound a b (pow2 n);
  Math.pow2_plus n n

val u32_product_bound : a:nat{a < pow2 32} -> b:nat{b < pow2 32} ->
  Lemma (UInt.size (a * b) 64 /\ a * b < pow2 64 - pow2 32 - 1)
let u32_product_bound a b =
  uint_product_bound #32 a b

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
  let r = { low = u32_combine x1y x0yl;
            high = U64.shift_right x1y u32_32; } in
  u64_32_digits x;
  //assert (U64.v x == U64.v x1 * pow2 32 + U64.v x0);
  assert (U64.v x0y == U64.v x0 * U32.v y);
  u64_32_digits x0y;
  //assert (U64.v x0y == U64.v x0yh * pow2 32 + U64.v x0yl);
  assert (U64.v x1y' == U64.v x / pow2 32 * U32.v y);
  mul32_digits (U64.v x) (U32.v y);
  assert (U64.v x * U32.v y == U64.v x1y' * pow2 32 + U64.v x0y);
  r

let l32 (x: UInt.uint_t 64) : UInt.uint_t 32 = x % pow2 32
let h32 (x: UInt.uint_t 64) : UInt.uint_t 32 = x / pow2 32

val mul32_bound : x:UInt.uint_t 32 -> y:UInt.uint_t 32 ->
    n:UInt.uint_t 64{n < pow2 64 - pow2 32 - 1 /\ n == x * y}
let mul32_bound x y =
  u32_product_bound x y;
  x * y

let pll (x y: U64.t) : n:UInt.uint_t 64{n < pow2 64 - pow2 32 - 1} =
  mul32_bound (l32 (U64.v x)) (l32 (U64.v y))
let plh (x y: U64.t) : n:UInt.uint_t 64{n < pow2 64 - pow2 32 - 1} =
  mul32_bound (l32 (U64.v x)) (h32 (U64.v y))
let phl (x y: U64.t) : n:UInt.uint_t 64{n < pow2 64 - pow2 32 - 1} =
  mul32_bound (h32 (U64.v x)) (l32 (U64.v y))
let phh (x y: U64.t) : n:UInt.uint_t 64{n < pow2 64 - pow2 32 - 1} =
  mul32_bound (h32 (U64.v x)) (h32 (U64.v y))

let pll_l (x y: U64.t) : UInt.uint_t 32 =
  l32 (pll x y)
let pll_h (x y: U64.t) : UInt.uint_t 32 =
  h32 (pll x y)

let mul_wide_low (x y: U64.t) = (plh x y + (phl x y + pll_h x y) % pow2 32) * pow2 32 % pow2 64 + pll_l x y

let mul_wide_high (x y: U64.t) =
  phh x y +
    (phl x y + pll_h x y) / pow2 32 +
    (plh x y + (phl x y + pll_h x y) % pow2 32) / pow2 32

inline_for_extraction noextract
let mul_wide_impl_t' (x y: U64.t) : Pure (tuple4 U64.t U64.t U64.t U64.t)
  (requires True)
  (ensures (fun r -> let (u1, w3, x', t') = r in
    U64.v u1 == U64.v x % pow2 32 /\
    U64.v w3 == pll_l x y /\
    U64.v x' == h32 (U64.v x) /\
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
let u32_combine' (hi lo: U64.t) : Pure U64.t
  (requires (U64.v lo < pow2 32))
  (ensures (fun r -> U64.v r = U64.v hi * pow2 32 % pow2 64 + U64.v lo)) =
  U64.add lo (U64.shift_left hi u32_32)

inline_for_extraction noextract
let mul_wide_impl (x: U64.t) (y: U64.t) :
    Tot (r:t{U64.v r.low == mul_wide_low x y /\
             U64.v r.high == mul_wide_high x y % pow2 64}) =
  let (u1, w3, x', t') = mul_wide_impl_t' x y in
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
  assert (U64.v r1 == (phh x y + (phl x y + pll_h x y) / pow2 32 + (plh x y + (phl x y + pll_h x y) % pow2 32) / pow2 32) % pow2 64);
  let r = { low = r0; high = r1; } in
  r

let product_sums (a b c d:nat) :
  Lemma ((a + b) * (c + d) == a * c + a * d + b * c + b * d) = ()

val u64_32_product (xl xh yl yh:UInt.uint_t 32) :
  Lemma ((xl + xh * pow2 32) * (yl + yh * pow2 32) ==
  xl * yl + (xl * yh) * pow2 32 + (xh * yl) * pow2 32 + (xh * yh) * pow2 64)
#push-options "--z3rlimit 25"
let u64_32_product xl xh yl yh =
  assert (xh >= 0); //flakiness; without this, can't prove that (xh * pow2 32) >= 0
  assert (pow2 32 >= 0); //flakiness; without this, can't prove that (xh * pow2 32) >= 0
  assert (xh*pow2 32 >= 0);
  product_sums xl (xh*pow2 32) yl (yh*pow2 32);
  mul_abc_to_acb xh (pow2 32) yl;
  assert (xl * (yh * pow2 32) == (xl * yh) * pow2 32);
  Math.pow2_plus 32 32;
  assert ((xh * pow2 32) * (yh * pow2 32) == (xh * yh) * pow2 64)
#pop-options

let product_expand (x y: U64.t) :
  Lemma (U64.v x * U64.v y == phh x y * pow2 64 +
                              (plh x y + phl x y + pll_h x y) * pow2 32 +
                              pll_l x y) =
  assert (U64.v x == l32 (U64.v x) + h32 (U64.v x) * pow2 32);
  assert (U64.v y == l32 (U64.v y) + h32 (U64.v y) * pow2 32);
  u64_32_product (l32 (U64.v x)) (h32 (U64.v x)) (l32 (U64.v y)) (h32 (U64.v y))

let product_low_expand (x y: U64.t) :
  Lemma ((U64.v x * U64.v y) % pow2 64 ==
    ((plh x y + phl x y + pll_h x y) * pow2 32 + pll_l x y) % pow2 64) =
  product_expand x y;
  Math.lemma_mod_plus ((plh x y + phl x y + pll_h x y) * pow2 32 + pll_l x y) (phh x y) (pow2 64)

let add_mod_then_mod (n m:nat) (k:pos) :
  Lemma ((n + m % k) % k == (n + m) % k) =
  mod_add n m k;
  mod_add n (m % k) k;
  mod_double m k

let shift_add (n:nat) (m:nat{m < pow2 32}) :
  Lemma (n * pow2 32 % pow2 64 + m == (n * pow2 32 + m) % pow2 64) =
  add_mod_small' m (n*pow2 32) (pow2 64)

let mul_wide_low_ok (x y: U64.t) :
  Lemma (mul_wide_low x y == (U64.v x * U64.v y) % pow2 64) =
  Math.pow2_plus 32 32;
  mod_mul (plh x y + (phl x y + pll_h x y) % pow2 32) (pow2 32) (pow2 32);
  assert (mul_wide_low x y ==
          (plh x y + (phl x y + pll_h x y) % pow2 32) % pow2 32 * pow2 32 + pll_l x y);
  add_mod_then_mod (plh x y) (phl x y + pll_h x y) (pow2 32);
  assert (mul_wide_low x y == (plh x y + phl x y + pll_h x y) % pow2 32 * pow2 32 + pll_l x y);
  mod_mul (plh x y + phl x y + pll_h x y) (pow2 32) (pow2 32);
  shift_add (plh x y + phl x y + pll_h x y) (pll_l x y);
  assert (mul_wide_low x y == ((plh x y + phl x y + pll_h x y) * pow2 32 + pll_l x y) % pow2 64);
  product_low_expand x y

val product_high32 : x:U64.t -> y:U64.t ->
  Lemma ((U64.v x * U64.v y) / pow2 32 == phh x y * pow2 32 + plh x y + phl x y + pll_h x y)
#push-options "--z3rlimit 20"
let product_high32 x y =
  Math.pow2_plus 32 32;
  product_expand x y;
  Math.division_addition_lemma (plh x y + phl x y + pll_h x y) (pow2 32) (phh x y * pow2 32);
  mul_div_cancel (phh x y * pow2 32) (pow2 32);
  mul_div_cancel (plh x y + phl x y + pll_h x y) (pow2 32);
  Math.small_division_lemma_1 (pll_l x y) (pow2 32)
#pop-options

val product_high_expand : x:U64.t -> y:U64.t ->
  Lemma ((U64.v x * U64.v y) / pow2 64 == phh x y + (plh x y + phl x y + pll_h x y) / pow2 32)

#push-options "--z3rlimit 15 --retry 5" // sporadically fails
let product_high_expand x y =
  Math.pow2_plus 32 32;
  div_product (mul_wide_high x y) (pow2 32) (pow2 32);
  product_high32 x y;
  Math.division_addition_lemma (plh x y + phl x y + pll_h x y) (pow2 32) (phh x y);
  ()
#pop-options

val mod_spec_multiply : n:nat -> k:pos ->
  Lemma ((n - n%k) / k * k == n - n%k)
let mod_spec_multiply n k =
  Math.lemma_mod_spec2 n k

val mod_spec_mod (n:nat) (k:pos) : Lemma ((n - n%k) % k == 0)
let mod_spec_mod n k =
  assert (n - n%k == n / k * k);
  Math.multiple_modulo_lemma (n/k) k

let mul_injective (n m:nat) (k:pos) :
  Lemma (requires (n * k == m * k))
        (ensures (n == m)) = ()

val div_sum_combine1 : n:nat -> m:nat -> k:pos ->
  Lemma ((n / k + m / k) * k == (n - n % k) + (m - m % k))
let div_sum_combine1 n m k =
  Math.distributivity_add_left (n / k) (m / k) k;
  div_mod n k;
  div_mod m k;
  ()

let mod_0 (k:pos) :
  Lemma (0 % k == 0) = ()

let n_minus_mod_exact (n:nat) (k:pos) :
    Lemma ((n - n % k) % k == 0) =
    mod_spec_mod n k;
    mod_0 k

let sub_mod_gt_0 (n:nat) (k:pos) :
  Lemma (0 <= n - n % k) = ()

val sum_rounded_mod_exact : n:nat -> m:nat -> k:pos ->
  Lemma (((n - n%k) + (m - m%k)) / k * k == (n - n%k) + (m - m%k))
#push-options "--retry 5" // sporadically fails
let sum_rounded_mod_exact n m k =
  n_minus_mod_exact n k;
  n_minus_mod_exact m k;
  sub_mod_gt_0 n k;
  sub_mod_gt_0 m k;
  mod_add (n - n%k) (m - m%k) k;
  Math.div_exact_r ((n - n%k) + (m - m % k)) k
#pop-options

val div_sum_combine : n:nat -> m:nat -> k:pos ->
  Lemma (n / k + m / k == (n + (m - n % k) - m % k) / k)
#push-options "--retry 5" // sporadically fails
let div_sum_combine n m k =
  sum_rounded_mod_exact n m k;
  div_sum_combine1 n m k;
  mul_injective (n / k + m / k) (((n - n%k) + (m - m%k)) / k) k;
  assert (n + m - n % k - m % k == (n - n%k) + (m - m%k))
#pop-options

val sum_shift_carry : a:nat -> b:nat -> k:pos ->
  Lemma (a / k + (b + a%k) / k == (a + b) / k)
let sum_shift_carry a b k =
  div_sum_combine a (b+a%k) k;
//  assert (a / k + (b + a%k) / k == (a + b + (a % k - a % k) - (b + a%k) % k) / k);
//  assert ((a + b + (a % k - a % k) - (b + a%k) % k) / k == (a + b - (b + a%k) % k) / k);
  add_mod_then_mod b a k;
  Math.lemma_mod_spec (a+b) k

let mul_wide_high_ok (x y: U64.t) :
  Lemma ((U64.v x * U64.v y) / pow2 64 == mul_wide_high x y) =
  product_high_expand x y;
  sum_shift_carry (phl x y + pll_h x y) (plh x y) (pow2 32)

let product_div_bound (#n:pos) (x y: UInt.uint_t n) :
  Lemma (x * y / pow2 n < pow2 n) =
  Math.pow2_plus n n;
  product_bound x y (pow2 n);
  pow2_div_bound #(n+n) (x * y) n

let mul_wide (x y:U64.t) : Pure t
  (requires True)
  (ensures (fun r -> v r == U64.v x * U64.v y)) =
  mul_wide_low_ok x y;
  mul_wide_high_ok x y;
  product_div_bound (U64.v x) (U64.v y);
  Math.modulo_lemma (mul_wide_high x y) (pow2 64);
  mul_wide_impl x y
