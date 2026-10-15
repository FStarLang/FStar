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
module FStar.BV
open FStar.UInt

module U = FStar.UInt
module I = FStar.Int
module B = FStar.BitVector
module S = FStar.Seq

let bv_t (n : nat) = B.bv_t n

let bv_uext #n #i a =
  Seq.append (Seq.create i false) a

let bv_extract
  (#n: pos)
  (a: bv_t n)
  (i: nat{i < n})
  (j: nat{j <= i})
  : Tot (bv_t (i - j + 1)) =
  // Bitvectors store the MSB at index 0; convert inclusive LSB-based bounds
  // to a half-open sequence slice.
  S.slice a (n - 1 - i) (n - j)

let bv_concat #n #m a b = S.append a b

let bv_repeat (#n #i: pos) (a: bv_t n) : Tot (bv_t (i * n)) =
  S.init (i * n) (fun k -> S.index a (k % n))

let bv_sext (#n #i: pos) (a: bv_t n) : Tot (bv_t (i + n)) =
  S.append (S.create i (S.index a 0)) a

let int2bv = U.to_vec
let bv2int = U.from_vec
let sbv_to_int = I.from_vec
let sbv_to_int_int2bv #n num = I.inverse_num_lemma #n num

let int2bv_lemma_1 = U.to_vec_lemma_1
let int2bv_lemma_2 = U.to_vec_lemma_2
let inverse_vec_lemma = U.inverse_vec_lemma
let inverse_num_lemma = U.inverse_num_lemma

let int2bv_bv_uext (#n #i: pos)
  (a: uint_t n)
  : Lemma
    (ensures (bv_uext #n #i (int2bv #n a) == int2bv #(i + n) (U.zero_extends #n i a))) =
  let zero = B.zero_vec #i in
  assert (U.from_vec #i zero == 0);
  U.append_lemma #i #n zero (int2bv #n a);
  assert (U.from_vec #(i + n) (bv_uext #n #i (int2bv #n a)) == a);
  ()

let int2bv_bv_extract #n a i j =
  let av = U.to_vec #n a in
  let w = i - j + 1 in
  let selected = bv_extract #n av i j in
  if j = 0
  then (
    if i = n - 1
    then U.inverse_num_lemma #n a
    else U.slice_right_lemma #n av w;
    U.inverse_num_lemma #n a
  )
  else (
    let prefix = S.slice av 0 (n - j) in
    U.slice_left_lemma #n av (n - j);
    if i = n - 1
    then (
      FStar.Math.Lemmas.small_mod
        (U.from_vec #(n - j) prefix) (pow2 (n - j))
    )
    else U.slice_right_lemma #(n - j) prefix w
  );
  let bits = (a / pow2 j) % pow2 w in
  assert (U.from_vec #w selected == bits);
  FStar.Math.Lemmas.lemma_mod_lt (a / pow2 j) (pow2 w);
  FStar.Math.Lemmas.small_mod bits (pow2 w);
  let model = U.to_uint_t w bits in
  assert (model == bits);
  U.inverse_num_lemma #w model;
  U.from_vec_lemma_2 selected (U.to_vec #w model)

let int2bv_bv_concat #n #m a b =
  U.append_lemma #n #m (int2bv #n a) (int2bv #m b);
  U.inverse_num_lemma #n a;
  U.inverse_num_lemma #m b;
  U.inverse_vec_lemma #(n + m)
    (bv_concat #n #m (int2bv #n a) (int2bv #m b))

private
let bv_repeat_init_append (#n: pos) (i: pos) (a: uint_t n)
  : Lemma
    (S.equal
      (S.init ((i + 1) * n)
        (fun k -> S.index (U.to_vec #n a) (k % n)))
      (S.append
        (S.init (i * n)
           (fun k -> S.index (U.to_vec #n a) (k % n)))
        (U.to_vec #n a))) =
  let lhs =
    S.init ((i + 1) * n)
      (fun k -> S.index (U.to_vec #n a) (k % n)) in
  let prefix =
    S.init (i * n)
      (fun k -> S.index (U.to_vec #n a) (k % n)) in
  let rhs = S.append prefix (U.to_vec #n a) in
  S.lemma_init_len ((i + 1) * n)
    (fun k -> S.index (U.to_vec #n a) (k % n));
  S.lemma_init_len (i * n)
    (fun k -> S.index (U.to_vec #n a) (k % n));
  S.lemma_len_append prefix (U.to_vec #n a);
  let pointwise (k:nat{k < S.length lhs})
    : Lemma (S.index lhs k == S.index rhs k) =
    if k < i * n
    then S.lemma_index_app1 prefix (U.to_vec #n a) k
    else (
      S.lemma_index_app2 prefix (U.to_vec #n a) k;
      FStar.Math.Lemmas.lemma_mod_plus
        (k - i * n) i n
    )
  in
  Classical.forall_intro pointwise;
  S.lemma_eq_intro lhs rhs

private
let bv_repeat_geometric_one (n: pos)
  : Lemma
    ((pow2 n - 1) / (pow2 n - 1) == 1) =
  FStar.Math.Lemmas.multiple_division_lemma 1 (pow2 n - 1)

private
let rec bv_repeat_geometric_identity (n: pos) (i: pos)
  : Lemma
    (((pow2 (i * n) - 1) / (pow2 n - 1)) * (pow2 n - 1)
     == pow2 (i * n) - 1)
    (decreases i) =
  if i = 1
  then bv_repeat_geometric_one n
  else (
    let p = i - 1 in
    bv_repeat_geometric_identity n p;
    FStar.Math.Lemmas.pow2_plus (p * n) n;
    assert (i * n == p * n + n);
    let d = pow2 n - 1 in
    let q = (pow2 (p * n) - 1) / d in
    assert (pow2 (p * n) - 1 == q * d);
    assert ((q * pow2 n + 1) * d == pow2 (i * n) - 1);
    FStar.Math.Lemmas.multiple_division_lemma (q * pow2 n + 1) d
  )

private
let bv_repeat_geometric_step (n: pos) (i: pos{i > 1})
  : Lemma
    ((pow2 (i * n) - 1) / (pow2 n - 1)
     == ((pow2 ((i - 1) * n) - 1) / (pow2 n - 1)) * pow2 n + 1) =
  let p = i - 1 in
  bv_repeat_geometric_identity n p;
  FStar.Math.Lemmas.pow2_plus (p * n) n;
  let d = pow2 n - 1 in
  let q = (pow2 (p * n) - 1) / d in
  assert (pow2 (p * n) - 1 == q * d);
  assert (i * n == p * n + n);
  assert (pow2 (i * n) - 1 == (q * pow2 n + 1) * d);
  FStar.Math.Lemmas.multiple_division_lemma (q * pow2 n + 1) d

private
let rec bv_repeat_from_vec (#n: pos) (i: pos) (a: uint_t n)
  : Lemma
    (U.from_vec #(i * n)
       (S.init (i * n)
         (fun k -> S.index (U.to_vec #n a) (k % n)))
     == a * ((pow2 (i * n) - 1) / (pow2 n - 1)))
    (decreases i) =
  if i = 1
  then (
    let repeated =
      S.init n (fun k -> S.index (U.to_vec #n a) (k % n)) in
    S.lemma_init_len n
      (fun k -> S.index (U.to_vec #n a) (k % n));
    S.lemma_eq_intro repeated (U.to_vec #n a);
    U.from_vec_lemma_1 #n repeated (U.to_vec #n a);
    U.inverse_num_lemma #n a;
    bv_repeat_geometric_one n;
    let goal_repeated =
      S.init (i * n)
        (fun k -> S.index (U.to_vec #n a) (k % n)) in
    S.lemma_init_len (i * n)
      (fun k -> S.index (U.to_vec #n a) (k % n));
    S.lemma_eq_intro goal_repeated repeated;
    S.lemma_eq_elim goal_repeated repeated
  )
  else (
    let p = i - 1 in
    let prefix =
      S.init (p * n)
        (fun k -> S.index (U.to_vec #n a) (k % n)) in
    let repeated =
      S.init (i * n)
        (fun k -> S.index (U.to_vec #n a) (k % n)) in
    let appended = S.append prefix (U.to_vec #n a) in
    assert (i == p + 1);
    bv_repeat_from_vec #n p a;
    assert
      (U.from_vec #(p * n) prefix
       == a * ((pow2 (p * n) - 1) / (pow2 n - 1)));
    bv_repeat_init_append #n p a;
    S.lemma_init_len (i * n)
      (fun k -> S.index (U.to_vec #n a) (k % n));
    S.lemma_init_len (p * n)
      (fun k -> S.index (U.to_vec #n a) (k % n));
    S.lemma_len_append prefix (U.to_vec #n a);
    assert (S.equal repeated appended);
    U.from_vec_lemma_1 #(i * n) repeated appended;
    U.append_lemma #(p * n) #n prefix (U.to_vec #n a);
    U.inverse_num_lemma #n a;
    assert
      (U.from_vec #(i * n) repeated
       == (a * ((pow2 (p * n) - 1) / (pow2 n - 1))) * pow2 n + a);
    bv_repeat_geometric_step n i;
    FStar.Math.Lemmas.distributivity_add_right
      a (((pow2 (p * n) - 1) / (pow2 n - 1)) * pow2 n) 1;
    FStar.Math.Lemmas.paren_mul_right
      a ((pow2 (p * n) - 1) / (pow2 n - 1)) (pow2 n);
    assert
      (U.from_vec #(i * n) repeated
       == a * ((pow2 (i * n) - 1) / (pow2 n - 1)))
  )

let int2bv_bv_repeat #n #i a =
  let repeated =
    S.init (i * n) (fun k -> S.index (U.to_vec #n a) (k % n)) in
  bv_repeat_from_vec #n i a;
  let raw = a * ((pow2 (i * n) - 1) / (pow2 n - 1)) in
  assert (U.from_vec #(i * n) repeated == raw);
  FStar.Math.Lemmas.small_mod raw (pow2 (i * n));
  let model = U.to_uint_t (i * n) raw in
  assert (model == raw);
  U.inverse_num_lemma #(i * n) model;
  U.from_vec_lemma_2 repeated (U.to_vec #(i * n) model);
  S.lemma_eq_elim repeated (U.to_vec #(i * n) model);
  assert (bv_repeat #n #i (int2bv #n a) == repeated)
    by (FStar.Tactics.norm
          [FStar.NormSteps.delta_only [`%bv_repeat; `%int2bv]])

let signed_int2bv_bv_sext #n #i a =
  let av = int2bv #n (I.to_uint #n a) in
  let extended = bv_sext #n #i av in
  assert (av == I.to_vec #n a)
    by (FStar.Tactics.norm
          [FStar.NormSteps.delta_only [`%int2bv; `%I.to_vec]]);
  assert (extended == S.append (S.create i (S.index av 0)) av)
    by (FStar.Tactics.norm
          [FStar.NormSteps.delta_only [`%bv_sext]]);
  U.inverse_num_lemma #n (I.to_uint #n a);
  U.append_lemma #i #n (S.create i (S.index av 0)) av;
  FStar.Math.Lemmas.pow2_plus i n;
  if a < 0
  then (
    if n = 1
    then ()
    else I.sign_bit_negative #n a;
    assert (S.index av 0 == true);
    assert_norm (S.create i (S.index av 0) == B.ones_vec #i);
    U.ones_from_vec_lemma #i;
    assert (U.from_vec #(i + n) extended == a + pow2 (i + n));
    assert (I.from_vec #(i + n) extended == a);
    assert (I.to_int_t (i + n) a == a)
  )
  else (
    if n = 1
    then ()
    else I.sign_bit_positive #n a;
    assert (S.index av 0 == false);
    assert_norm (S.create i (S.index av 0) == B.zero_vec #i);
    U.zero_from_vec_lemma #i;
    assert (U.from_vec #(i + n) extended == a);
    assert (I.from_vec #(i + n) extended == a);
    assert (I.to_int_t (i + n) a == a)
  );
  assert
    (I.from_vec #(i + n) extended == I.to_int_t (i + n) a);
  I.inverse_vec_lemma #(i + n) extended;
  S.lemma_eq_elim extended
    (I.to_vec #(i + n) (I.from_vec #(i + n) extended))

(** Mapping an unbounded nat to a bitvector; only used for bvshl and bvshr
  compatibility funs *)
let int2bv_nat (#n: pos) (num: nat): Tot (bv_t n) = U.to_vec (num % pow2 n)

let int2bv_nat_lemma (#n: pos) (num: uint_t n)
    : Lemma
      (ensures (int2bv_nat #n num == int2bv #n num)) =
  assert (num < pow2 n);
  FStar.Math.Lemmas.modulo_lemma num (pow2 n);
  assert (num % pow2 n = num)

let list2bv #n l = S.seq_of_list l
let bv2list #n s = S.seq_to_list s
let list2bv_bij #n a = S.lemma_list_seq_bij a
let bv2list_bij #n a = S.lemma_seq_list_bij a

let bvand = B.logand_vec
let int2bv_logand #n #x #y #z pf =
  inverse_vec_lemma #n (bvand #n (int2bv #n x) (int2bv #n y))

let bvxor = B.logxor_vec
let int2bv_logxor #n #x #y #z pf =
  inverse_vec_lemma #n (bvxor #n (int2bv x) (int2bv y))

let bvor = B.logor_vec
let int2bv_logor #n #x #y #z pf =
  inverse_vec_lemma #n (bvor #n (int2bv x) (int2bv y))

let bvnot = B.lognot_vec
let int2bv_lognot #n #x #y pf =
  inverse_vec_lemma #n (bvnot #n (int2bv x))

let bvneg #n a =
  int2bv #n (I.to_uint #n (I.to_int_t n (- sbv_to_int #n a)))
let signed_int2bv_bvneg #n num =
  sbv_to_int_int2bv #n num
let bvnand #n a b = bvnot #n (bvand #n a b)
let int2bv_bvnand #n a b =
  int2bv_logand #n #a #b #(bvand #n (int2bv #n a) (int2bv #n b)) ();
  int2bv_lognot #n #(U.logand #n a b)
    #(bvnand #n (int2bv #n a) (int2bv #n b)) ()
let bvnor #n a b = bvnot #n (bvor #n a b)
let int2bv_bvnor #n a b =
  int2bv_logor #n #a #b #(bvor #n (int2bv #n a) (int2bv #n b)) ();
  int2bv_lognot #n #(U.logor #n a b)
    #(bvnor #n (int2bv #n a) (int2bv #n b)) ()
let bvxnor #n a b = bvnot #n (bvxor #n a b)
let int2bv_bvxnor #n a b =
  int2bv_logxor #n #a #b #(bvxor #n (int2bv #n a) (int2bv #n b)) ();
  int2bv_lognot #n #(U.logxor #n a b)
    #(bvxnor #n (int2bv #n a) (int2bv #n b)) ()
let bvcomp #n a b = if a = b then int2bv #1 1 else int2bv #1 0
let int2bv_bvcomp #n a b =
  U.inverse_num_lemma #n a;
  U.inverse_num_lemma #n b

(*TODO: specify index functions? *)
let bvshl' (#n: pos) (a: bv_t n) (s: bv_t n): bv_t n =
  B.shift_left_vec #n a (bv2int #n s)
let bvshl (#n: pos) (a: bv_t n) (s: nat): bv_t n =
  bvshl' #n a (int2bv_nat #n s)

let int2bv_shl' #n #x #y #z pf =
  inverse_vec_lemma #n (bvshl' #n (int2bv #n x) (int2bv #n y))
let int2bv_shl #n #x #y #z pf =
  int2bv_nat_lemma #n y;
  inverse_vec_lemma #n (bvshl #n (int2bv #n x) y)

let bvshr' (#n: pos) (a: bv_t n) (s: bv_t n): bv_t n =
  B.shift_right_vec #n a (bv2int #n s)
let bvshr (#n: pos) (a: bv_t n) (s: nat) : bv_t n =
  bvshr' #n a (int2bv_nat #n s)
let int2bv_shr' #n #x #y #z pf =
  inverse_vec_lemma #n (bvshr' #n (int2bv #n x) (int2bv #n y))
let int2bv_shr #n #x #y #z pf =
  int2bv_nat_lemma #n y;
  inverse_vec_lemma #n (bvshr #n (int2bv #n x) y)

let bvashr (#n: pos) (a s: bv_t n): bv_t n =
  B.shift_arithmetic_right_vec #n a (bv2int #n s)
let signed_int2bv_bvashr #n a s =
  U.inverse_num_lemma #n s;
  I.inverse_vec_lemma #n
    (bvashr #n (int2bv #n (I.to_uint #n a)) (int2bv #n s))

(* Rotate operations *)
let bvrol' (#n: pos) (a: bv_t n) (s: bv_t n): bv_t n =
  B.rotate_left_vec #n a (bv2int #n s)
let bvrol (#n: pos) (a: bv_t n) (s: nat): bv_t n =
  bvrol' #n a (int2bv_nat #n s)

let int2bv_rol' #n #x #y #z pf =
  inverse_vec_lemma #n (bvrol' #n (int2bv #n x) (int2bv #n y))
let int2bv_rol #n #x #y #z pf =
  int2bv_nat_lemma #n y;
  inverse_vec_lemma #n (bvrol #n (int2bv #n x) y)

let bvror' (#n: pos) (a: bv_t n) (s: bv_t n): bv_t n =
  B.rotate_right_vec #n a (bv2int #n s)
let bvror (#n: pos) (a: bv_t n) (s: nat): bv_t n =
  bvror' #n a (int2bv_nat #n s)

let int2bv_ror' #n #x #y #z pf =
  inverse_vec_lemma #n (bvror' #n (int2bv #n x) (int2bv #n y))
let int2bv_ror #n #x #y #z pf =
  int2bv_nat_lemma #n y;
  inverse_vec_lemma #n (bvror #n (int2bv #n x) y)



let bvult #n a b = (bv2int #n a) < (bv2int #n b)

let int2bv_lemma_ult_1 #n a b =
  inverse_num_lemma #n a;
  inverse_num_lemma #n b

let int2bv_lemma_ult_2 #n a b =
  inverse_num_lemma #n a;
  inverse_num_lemma #n b

let bvule #n a b = bv2int #n a <= bv2int #n b
let bvugt #n a b = bv2int #n a > bv2int #n b
let bvuge #n a b = bv2int #n a >= bv2int #n b
let int2bv_bvule #n a b =
  inverse_num_lemma #n a;
  inverse_num_lemma #n b
let int2bv_bvugt #n a b =
  inverse_num_lemma #n a;
  inverse_num_lemma #n b
let int2bv_bvuge #n a b =
  inverse_num_lemma #n a;
  inverse_num_lemma #n b

let bvslt #n a b = sbv_to_int #n a < sbv_to_int #n b
let bvsle #n a b = sbv_to_int #n a <= sbv_to_int #n b
let bvsgt #n a b = sbv_to_int #n a > sbv_to_int #n b
let bvsge #n a b = sbv_to_int #n a >= sbv_to_int #n b
let signed_int2bv_comparisons #n a b =
  sbv_to_int_int2bv #n a;
  sbv_to_int_int2bv #n b


let bvadd #n a b =
    int2bv #n (U.add_mod (bv2int #n a) (bv2int #n b))
let int2bv_add #n #x #y #z pf =
  inverse_vec_lemma #n (bvadd #n (int2bv #n x) (int2bv #n y))

let bvsub #n a b =
    int2bv #n (U.sub_mod (bv2int #n a) (bv2int #n b))
let int2bv_sub #n #x #y #z pf =
  inverse_vec_lemma #n (bvsub #n (int2bv #n x) (int2bv #n y))

let bvdiv #n a b =
    int2bv #n (U.udiv #n (bv2int #n a) b)
let int2bv_div #n #x #y #z pf =
  inverse_vec_lemma #n (bvdiv #n (int2bv #n x) y)

let bvdiv_unsafe #n a b =
  if bv2int b <> 0 then bvdiv a (bv2int b) else int2bv #n (pow2 n - 1)
let bvdiv_unsafe_sound #n #a #b b_nonzero_pf = ()


let bvmod #n a b =
    int2bv #n (U.mod #n (bv2int #n a) b)
let int2bv_mod #n #x #y #z pf =
  inverse_vec_lemma #n (bvmod #n (int2bv #n x) y)

let bvmod_unsafe #n a b =
  if bv2int b <> 0 then bvmod a (bv2int b) else a
let bvmod_unsafe_sound #n #a #b b_nonzero_pf = ()

// Z3's bvmul is also modulo
let bvmul #n a b =
  int2bv #n (U.mul_mod #n (bv2int #n a) b)
let int2bv_mul #n #x #y #z pf =
  inverse_vec_lemma #n (bvmul #n (int2bv #n x) y)

let bvmul' #n a b =
  int2bv #n (U.mul_mod #n (bv2int #n a) (bv2int #n b))

let int2bv_mul' #n #x #y #z pf =
  inverse_vec_lemma #n (bvmul' #n (int2bv #n x) (int2bv #n y))

let bvsdiv #n a b =
  let x = sbv_to_int #n a in
  let y = sbv_to_int #n b in
  if y = 0
  then int2bv #n (I.to_uint #n (I.to_int_t n (if x < 0 then 1 else -1)))
  else int2bv #n (I.to_uint #n (I.to_int_t n I.(x /- y)))

let bvsrem #n a b =
  let x = sbv_to_int #n a in
  let y = sbv_to_int #n b in
  if y = 0
  then a
  else int2bv #n (I.to_uint #n (x - (I.(x /- y) * y)))

let bvsmod #n a b =
  let x = sbv_to_int #n a in
  let y = sbv_to_int #n b in
  if y = 0
  then a
  else
    let r = x - (I.(x /- y) * y) in
    int2bv #n
      (I.to_uint #n
        (I.to_int_t n
          (if r = 0 || (r < 0) = (y < 0) then r else r + y)))

let signed_int2bv_bvsdiv #n a b =
  sbv_to_int_int2bv #n a;
  sbv_to_int_int2bv #n b
let signed_int2bv_bvsrem #n a b =
  sbv_to_int_int2bv #n a;
  sbv_to_int_int2bv #n b
let signed_int2bv_bvsmod #n a b =
  sbv_to_int_int2bv #n a;
  sbv_to_int_int2bv #n b

let bvnego #n a = sbv_to_int #n a = I.min_int n
let bvuaddo #n a b = bv2int #n a + bv2int #n b >= pow2 n
let bvsaddo #n a b = not (I.fits (sbv_to_int #n a + sbv_to_int #n b) n)
let bvumulo #n a b = bv2int #n a * bv2int #n b >= pow2 n
let bvsmulo #n a b = not (I.fits (sbv_to_int #n a * sbv_to_int #n b) n)
let bvusubo #n a b = bv2int #n a < bv2int #n b
let bvssubo #n a b = not (I.fits (sbv_to_int #n a - sbv_to_int #n b) n)
let bvsdivo #n a b =
  sbv_to_int #n a = I.min_int n && sbv_to_int #n b = -1

let signed_int2bv_bvnego #n a =
  sbv_to_int_int2bv #n a
let int2bv_bvuaddo #n a b =
  inverse_num_lemma #n a;
  inverse_num_lemma #n b
let signed_int2bv_bvsaddo #n a b =
  sbv_to_int_int2bv #n a;
  sbv_to_int_int2bv #n b
let int2bv_bvumulo #n a b =
  inverse_num_lemma #n a;
  inverse_num_lemma #n b
let signed_int2bv_bvsmulo #n a b =
  sbv_to_int_int2bv #n a;
  sbv_to_int_int2bv #n b
let int2bv_bvusubo #n a b =
  inverse_num_lemma #n a;
  inverse_num_lemma #n b
let signed_int2bv_bvssubo #n a b =
  sbv_to_int_int2bv #n a;
  sbv_to_int_int2bv #n b
let signed_int2bv_bvsdivo #n a b =
  sbv_to_int_int2bv #n a;
  sbv_to_int_int2bv #n b
