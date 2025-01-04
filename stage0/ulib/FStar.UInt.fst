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
module FStar.UInt

(* NOTE: anything that you fix/update here should be reflected in [FStar.Int.fst], which is mostly
 * a copy-paste of this module. *)

open FStar.Mul
open FStar.BitVector
open FStar.Math.Lemmas

let pow2_values x =
   match x with
   | 0  -> assert_norm (pow2 0 == 1)
   | 1  -> assert_norm (pow2 1 == 2)
   | 8  -> assert_norm (pow2 8 == 256)
   | 16 -> assert_norm (pow2 16 == 65536)
   | 31 -> assert_norm (pow2 31 == 2147483648)
   | 32 -> assert_norm (pow2 32 == 4294967296)
   | 63 -> assert_norm (pow2 63 == 9223372036854775808)
   | 64 -> assert_norm (pow2 64 == 18446744073709551616)
   | 128 -> assert_norm (pow2 128 = 0x100000000000000000000000000000000)
   | _  -> ()

let incr_underspec #n a =
  if a < max_int n then a + 1 else 0

let decr_underspec #n a =
  if a > min_int n then a - 1 else 0

let add_underspec #n a b =
  if fits (a+b) n then a + b else 0

let sub_underspec #n a b =
  if fits (a-b) n then a - b else 0

let mul_underspec #n a b =
  if fits (a*b) n then a * b else 0

#push-options "--fuel 0 --ifuel 0"
let lt_square_div_lt a b = ()

let div_underspec #n a b =
  if fits (a / b) n then a / b else 0
#pop-options

let div_size #n a b =
  FStar.Math.Lib.slash_decr_axiom a b; ()

open FStar.Seq

let to_vec_lemma_1 #n a b = ()

let rec to_vec_lemma_2 #n a b =
  if n = 0 then () else begin
    assert(equal (slice (to_vec b) 0 (n - 1)) (to_vec #(n - 1) (b / 2)));
    assert(equal (slice (to_vec a) 0 (n - 1)) (to_vec #(n - 1) (a / 2)));
    to_vec_lemma_2 #(n - 1) (a / 2) (b / 2);
    assert(a % 2 = (if index (to_vec a) (n - 1) then 1 else 0));
    assert(b % 2 = (if index (to_vec b) (n - 1) then 1 else 0));
    assert(a % 2 = b % 2)
  end

let rec inverse_aux #n vec i =
  if i = n - 1 then
    assert((from_vec vec) % 2 = (if index vec (n - 1) then 1 else 0))
  else inverse_aux #(n - 1) (slice vec 0 (n - 1)) i

let inverse_vec_lemma #n vec = ()

let inverse_num_lemma #n num = to_vec_lemma_2 #n num (from_vec (to_vec num))

let from_vec_lemma_1 #n a b = ()

let from_vec_lemma_2 #n a b = inverse_vec_lemma a; inverse_vec_lemma b

#push-options "--fuel 0 --ifuel 0"
let from_vec_aux #n a s1 s2 =
  paren_mul_left (from_vec #s2 (slice a 0 s2)) (pow2 (s1 - s2)) (pow2 (n - s1));
  paren_mul_right (from_vec #s2 (slice a 0 s2)) (pow2 (s1 - s2)) (pow2 (n - s1));
  pow2_plus (s1 - s2) (n - s1)
#pop-options

let seq_slice_lemma #n a s1 t1 s2 t2 = ()

#push-options "--initial_fuel 1 --max_fuel 1"
let rec from_vec_propriety #n a s =
  if s = n - 1 then () else begin
    from_vec_propriety #n a (s + 1);
    from_vec_propriety #(s + 1) (slice a 0 (s + 1)) s;
    seq_slice_lemma #n a 0 (s + 1) 0 s;
    seq_slice_lemma #n a 0 (s + 1) s (s + 1);
    from_vec_aux #n a (s + 1) s;
    from_vec_propriety #(n - s) (slice a s n) 1;
    seq_slice_lemma #n a s n 0 1;
    seq_slice_lemma #n a s n 1 (n - s)
  end
#pop-options

let append_lemma #n #m a b =
  assert(equal a (slice (append a b) 0 n));
  assert(equal b (slice (append a b) n (n + m)));
  from_vec_propriety #(n + m) (append a b) n

let slice_left_lemma #n a s =
  from_vec_propriety #n a s;
  division_addition_lemma (from_vec #(n - s) (slice a s n)) (pow2 (n - s)) (from_vec #s (slice a 0 s));
  small_division_lemma_1 (from_vec #(n - s) (slice a s n)) (pow2 (n - s))

let slice_right_lemma #n a s =
  from_vec_propriety #n a (n - s);
  modulo_addition_lemma (from_vec #s (slice a (n - s) n)) (pow2 s) (from_vec #(n - s) (slice a 0 (n - s)));
  small_modulo_lemma_1 (from_vec #s (slice a (n - s) n)) (pow2 s)

let rec zero_to_vec_lemma #n i =
  if i = n - 1 then () else zero_to_vec_lemma #(n - 1) i

let zero_from_vec_lemma #n = to_vec_lemma_2 (from_vec (zero_vec #n)) (zero n)

let one_to_vec_lemma #n i =
  if i = n - 1 then () else zero_to_vec_lemma #n i

let rec pow2_to_vec_lemma #n p i =
  if i = n - 1 then ()
  else if p = 0 then one_to_vec_lemma #n i
  else pow2_to_vec_lemma #(n - 1) (p - 1) i

let pow2_from_vec_lemma #n p =
  to_vec_lemma_2 (from_vec (elem_vec #n p)) (pow2_n #n (n - p - 1))

let rec ones_to_vec_lemma #n i =
  if i = n - 1 then () else ones_to_vec_lemma #(n - 1) i

let ones_from_vec_lemma #n =
  to_vec_lemma_2 (from_vec (ones_vec #n)) (ones n)

let nth_lemma #n a b =
  assert(forall (i:nat{i < n}). index (to_vec #n a) i = index (to_vec #n b) i);
  to_vec_lemma_2 a b

let zero_nth_lemma #n i = ()

let pow2_nth_lemma #n p i = ()

let one_nth_lemma #n i = ()

let ones_nth_lemma #n i = ()

let logand_definition #n a b i = ()

let logxor_definition #n a b i = ()

let logor_definition #n a b i = ()

let lognot_definition #n a i = ()

let logand_commutative #n a b = nth_lemma #n (logand #n a b) (logand #n b a)

let logand_associative #n a b c = nth_lemma #n (logand #n (logand #n a b) c) (logand #n a (logand #n b c))

let logand_self #n a = nth_lemma #n (logand #n a a) a

let logand_lemma_1 #n a = nth_lemma #n (logand #n a (zero n)) (zero n)

let logand_lemma_2 #n a = nth_lemma #n (logand #n a (ones n)) a

let rec subset_vec_le_lemma #n a b = match n with
  | 1 -> ()
  | _ -> lemma_slice_subset_vec #n a b 0 (n-1);
        subset_vec_le_lemma #(n-1) (slice a 0 (n-1)) (slice b 0 (n-1))

let logand_le #n a b =
  let va = to_vec a in
  let vb = to_vec b in
  let vand = to_vec (logand a b) in
  subset_vec_le_lemma #n vand va;
  subset_vec_le_lemma #n vand vb

let logxor_commutative #n a b = nth_lemma #n (logxor #n a b) (logxor #n b a)

let logxor_associative #n a b c = nth_lemma #n (logxor #n (logxor #n a b) c) (logxor #n a (logxor #n b c))

let logxor_self #n a = nth_lemma #n (logxor #n a a) (zero n)

let logxor_lemma_1 #n a = nth_lemma #n (logxor #n a (zero n)) a

let logxor_lemma_2 #n a = nth_lemma #n (logxor #n a (ones n)) (lognot #n a)

let xor_lemma _ _ = ()

let logxor_inv #n a b =
  let open FStar.BitVector in
  let open FStar.Seq in
  let va = to_vec a in
  let vb = to_vec b in
  cut(forall (i:nat). i < n ==> index (logxor_vec #n va vb) i = (index va i <> index vb i));
  cut (forall (i:nat). {:pattern (index (logxor_vec (logxor_vec va vb) vb) i)}
    i < n ==> index (logxor_vec (logxor_vec va vb) vb) i = (xor (xor (index va i)
                                                                    (index vb i))
                                                               (index vb i)));
  cut (forall (i:nat). i < n ==> index (logxor_vec (logxor_vec va vb) vb) i = index va i);
  Seq.lemma_eq_intro (logxor_vec (logxor_vec va vb) vb) va;
  inverse_num_lemma a; inverse_num_lemma b

let logxor_neq_nonzero #n a b =
  let va = to_vec a in
  let vb = to_vec b in
  if logxor a b = 0 then
  begin
    let open FStar.Seq in
    let f (i:nat{i < n}) : Lemma (not (nth #n 0 i)) = zero_nth_lemma #n i in
    Classical.forall_intro f;
    assert (forall (i:nat{i < n}). index va i = index vb i);
    lemma_eq_intro va vb;
    assert (from_vec va = from_vec vb)
  end

let logor_commutative #n a b = nth_lemma #n (logor #n a b) (logor #n b a)

let logor_associative #n a b c = nth_lemma #n (logor #n (logor #n a b) c) (logor #n a (logor #n b c))

let logor_self #n a = nth_lemma #n (logor #n a a) a

let logor_lemma_1 #n a = nth_lemma (logor #n a (zero n)) a

let logor_lemma_2 #n a = nth_lemma (logor #n a (ones n)) (ones n)

let rec superset_vec_ge_lemma #n a b = match n with
  | 1 -> ()
  | _ -> lemma_slice_superset_vec #n a b 0 (n-1);
        superset_vec_ge_lemma #(n-1) (slice a 0 (n-1)) (slice b 0 (n-1))

let logor_ge #n a b =
  let va = to_vec a in
  let vb = to_vec b in
  let vor = to_vec (logor a b) in
  superset_vec_ge_lemma #n vor va;
  superset_vec_ge_lemma #n vor vb

let lognot_self #n a = nth_lemma (lognot #n (lognot #n a)) a

let lognot_lemma_1 #n = nth_lemma (lognot #n (zero n)) (ones n)

val to_vec_mod_pow2: #n:nat -> a:uint_t n -> m:pos -> i:nat{n - m <= i /\ i < n} ->
  Lemma (requires (a % pow2 m == 0))
        (ensures  (index (to_vec a) i == false))
        [SMTPat (index (to_vec #n a) i); SMTPat (pow2 m)]
let rec to_vec_mod_pow2 #n a m i =
  if i = n - 1 then
    begin
    lemma_index_app2 (to_vec #(n - 1) (a / 2)) (Seq.create 1 (a % 2 = 1)) i;
    mod_mult_exact a 2 (pow2 (m - 1))
    end
  else
    begin
    lemma_index_app1 (to_vec #(n - 1) (a / 2)) (Seq.create 1 (a % 2 = 1)) i;
    assert (index (to_vec a) i == index (to_vec #(n - 1) (a / 2)) i);
    mod_pow2_div2 a m;
    to_vec_mod_pow2 #(n - 1) (a / 2) (m - 1) i
    end

val to_vec_lt_pow2: #n:nat -> a:uint_t n -> m:nat -> i:nat{i < n - m} ->
  Lemma (requires (a < pow2 m))
        (ensures  (index (to_vec a) i == false))
        [SMTPat (index (to_vec #n a) i); SMTPat (pow2 m)]
let rec to_vec_lt_pow2 #n a m i =
  if n = 0 then ()
  else
    if m = 0 then
      assert (a == zero n)
    else
      begin
      lemma_index_app1 (to_vec #(n - 1) (a / 2)) (Seq.create 1 (a % 2 = 1)) i;
      assert (index (to_vec a) i == index (to_vec #(n - 1) (a / 2)) i);
      to_vec_lt_pow2 #(n - 1) (a / 2) (m - 1) i
      end

(** Used in the next two lemmas *)
#push-options "--initial_fuel 0 --max_fuel 1 --z3rlimit 40"
let rec index_to_vec_ones #n m i =
   let a = pow2 m - 1 in
   pow2_le_compat n m;
   if m = 0 then one_to_vec_lemma #n i
   else if m = n then ones_to_vec_lemma #n i
   else if i = n - 1 then ()
   else index_to_vec_ones #(n - 1) (m - 1) i
#pop-options

let logor_disjoint #n a b m =
  assert (a % pow2 m == 0); // To trigger pattern above
  assert (forall (i:nat{n - m <= i /\ i < n}).{:pattern (index (to_vec a) i)}
    index (to_vec a) i == false);
  assert (b < pow2 m); // To trigger pattern above
  assert (forall (i:nat{i < n - m}).{:pattern (index (to_vec b) i)}
    index (to_vec b) i == false);
  Seq.lemma_split (logor_vec (to_vec a) (to_vec b)) (n - m);
  Seq.lemma_eq_intro
    (logor_vec (to_vec a) (to_vec b))
    (append (slice (to_vec a) 0 (n - m)) (slice (to_vec b) (n - m) n));
  append_lemma #(n - m) #m (slice (to_vec a) 0 (n - m)) (slice (to_vec b) (n - m) n);
  slice_left_lemma #n (to_vec a) (n - m);
  div_exact_r a (pow2 m);
  assert (from_vec #(n - m) (slice (to_vec a) 0 (n - m)) * pow2 m == a);
  slice_right_lemma #n (to_vec b) m;
  small_modulo_lemma_1 b (pow2 m);
  assert (from_vec #m (slice (to_vec b) (n - m) n) == b)

let logand_mask #n a m =
  pow2_lt_compat n m;
  Seq.lemma_split (logand_vec (to_vec a) (to_vec (pow2 m - 1))) (n - m);
  Seq.lemma_eq_intro
    (logand_vec (to_vec a) (to_vec (pow2 m - 1)))
    (append (zero_vec #(n - m)) (slice (to_vec a) (n - m) n));
  append_lemma #(n - m) #m (zero_vec #(n - m)) (slice (to_vec a) (n - m) n);
  calc (==) {
    0 * pow2 m + a % pow2 m;
    == { }
    0 + a % pow2 m;
    == { }
    a % pow2 m;
  };
  assert (0 * pow2 m + a % pow2 m == a % pow2 m);
  assert (from_vec #(n - m) (zero_vec #(n - m)) == 0);
  slice_right_lemma #n (to_vec a) m;
  assert (from_vec #m (slice (to_vec a) (n - m) n) == a % pow2 m)

let shift_left_lemma_1 #n a s i = ()

let shift_left_lemma_2 #n a s i = ()

let shift_right_lemma_1 #n a s i = ()

let shift_right_lemma_2 #n a s i = ()

let shift_left_logand_lemma #n a b s = nth_lemma (shift_left #n (logand #n a b) s) (logand #n (shift_left #n a s) (shift_left #n b s))

let shift_right_logand_lemma #n a b s = nth_lemma (shift_right #n (logand #n a b) s) (logand #n (shift_right #n a s) (shift_right #n b s))

let shift_left_logxor_lemma #n a b s = nth_lemma (shift_left #n (logxor #n a b) s) (logxor #n (shift_left #n a s) (shift_left #n b s))

let shift_right_logxor_lemma #n a b s = nth_lemma (shift_right #n (logxor #n a b) s) (logxor #n (shift_right #n a s) (shift_right #n b s))

let shift_left_logor_lemma #n a b s = nth_lemma (shift_left #n (logor #n a b) s) (logor #n (shift_left #n a s) (shift_left #n b s))

let shift_right_logor_lemma #n a b s = nth_lemma (shift_right #n (logor #n a b) s) (logor #n (shift_right #n a s) (shift_right #n b s))


let shift_left_value_aux_1 #n a s = pow2_multiplication_modulo_lemma_1 a n s

let shift_left_value_aux_2 #n a =
  assert_norm(a * pow2 0 = a);
  small_modulo_lemma_1 a (pow2 n)

let shift_left_value_aux_3 #n a s =
  append_lemma #(n - s) #s (slice (to_vec a) s n) (zero_vec #s);
  slice_right_lemma #n (to_vec a) (n - s);
  pow2_multiplication_modulo_lemma_2 a n s

let shift_left_value_lemma #n a s =
  if s >= n then shift_left_value_aux_1 #n a s
  else if s = 0 then shift_left_value_aux_2 #n a
  else shift_left_value_aux_3 #n a s

let shift_right_value_aux_1 #n a s =
  pow2_le_compat s n;
  small_division_lemma_1 a (pow2 s)

let shift_right_value_aux_2 #n a = assert_norm (pow2 0 == 1)

#push-options "--z3rlimit 50"
let shift_right_value_aux_3 #n a s =
  append_lemma #s #(n - s) (zero_vec #s) (slice (to_vec a) 0 (n - s));
  slice_left_lemma #n (to_vec a) (n - s)
#pop-options

let shift_right_value_lemma #n a s =
  if s >= n then shift_right_value_aux_1 #n a s
  else if s = 0 then shift_right_value_aux_2 #n a
  else shift_right_value_aux_3 #n a s

#push-options "--z3rlimit 10"
let lemma_msb_pow2 #n a = if n = 1 then () else from_vec_propriety (to_vec a) 1
#pop-options

val plus_one_mod : p:pos -> a:nat ->
    Lemma (requires (a < p /\ ((a + 1) % p == 0))) (ensures (a == p - 1))
let plus_one_mod p a = ()

let lemma_minus_zero #n a =
  if minus a = 0 then
  begin
    plus_one_mod (pow2 n) (lognot a);
    lognot_self a;
    logxor_self (ones n);
    logxor_lemma_2 #n (ones n)
  end

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let lemma_msb_gte #n a b =
  from_vec_propriety (to_vec a) 1;
  from_vec_propriety (to_vec b) 1
#pop-options

(* Lemmas toward showing ~n + 1 = -a *)

// #set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

#push-options "--z3rlimit 80"
let lemma_uint_mod #n a = ()
#pop-options

let lemma_add_sub_cancel #n a b =
  let ab = (a-b) % pow2 n in
  let abb = (ab + b) % pow2 n in
  let ab_mod = sub_mod a b in
  let abb_mod = add_mod ab b in
  let p = pow2 n in
  lemma_uint_mod a;
  assert (add_mod (sub_mod a b) b = add_mod ab_mod b);
  assert (add_mod ab_mod b = (ab_mod + b) % p);
  assert (add_mod ab_mod b = ((a-b) % p + b) % p);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (a-b) b p;
  assert (((a-b) + b) % p = (((a-b) % p) + b) % p);
  assert (a % p = (((a-b) % p) + b) % p)

let lemma_mod_sub_distr_l a b p =
  let q = (a - (a % p)) / p in
  FStar.Math.Lemmas.lemma_mod_spec2 a p;
  FStar.Math.Lemmas.lemma_mod_plus (a % p - b) q p

let lemma_sub_add_cancel #n a b =
  let ab = (a+b) % pow2 n in
  let abb = (ab - b) % pow2 n in
  let ab_mod = add_mod a b in
  let abb_mod = sub_mod ab b in
  let p = pow2 n in
  lemma_uint_mod a;
  lemma_mod_sub_distr_l (a+b) b p

let lemma_zero_extend #n a =
  let hd0 = Seq.create 1 false in
  let av = to_vec a in
  let eav = Seq.append hd0 av in
  let r = zero_extend a in
  append_lemma #1 #n hd0 av;
  assert (r = from_vec eav);
  from_vec_propriety #(n+1) eav 1;
  assert (r = a)

#push-options "--z3rlimit 40"
let lemma_one_extend #n a =
  let hd1 = Seq.create 1 true in
  let av = to_vec a in
  let eav = Seq.append hd1 av in
  let r = one_extend a in
  append_lemma #1 #n hd1 av;
  assert (r = from_vec eav);
  from_vec_propriety #(n+1) eav 1;
  assert (r = pow2 n + a)
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
let lemma_lognot_zero_ext #n a =
  let lhs = lognot #(n+1) a in
  let rhs = pow2 n + (lognot #n a) in

  let av = to_vec a in
  assert (Seq.length av = n);
  let hd0 = Seq.create 1 false in
  let hd1 = Seq.create 1 true in
  let nav = to_vec (lognot a) in
  let eav = Seq.append hd0 av in

  append_lemma #1 #n hd0 av;
  assert (from_vec #(n+1) eav = op_Multiply (from_vec #1 hd0) (pow2 n) + from_vec av);
  assert (op_Multiply (from_vec #1 hd0) (pow2 n) = 0);
  assert (from_vec #(n+1) eav = from_vec #n av);
  assert (from_vec #(n+1) eav < pow2 n);

  let nav = BitVector.lognot_vec #n av in
  let neav_r = BitVector.lognot_vec #(n+1) eav in
  let neav_l = Seq.append hd1 nav in
  append_lemma #1 #n hd1 nav;
  assert (from_vec #(n+1) neav_l = (op_Multiply (from_vec #1 hd1) (pow2 n)) + (from_vec #n nav));
  assert (op_Multiply (from_vec #1 hd1) (pow2 n) = pow2 n);
  assert (from_vec #(n+1) neav_l = pow2 n + from_vec #n nav);
  assert (pow2 n + from_vec #n nav = rhs);

  assert (forall (i:pos{i < n+1}). Seq.index neav_r i = Seq.index neav_l i);
  Seq.Base.lemma_eq_intro neav_l neav_r;
  assert (neav_l = neav_r);
  assert (from_vec neav_r = lhs)

let lemma_lognot_one_ext #n a =
  let lhs = lognot #(n+1) (one_extend a) in
  let rhs = lognot #n a in
  let av = to_vec a in
  assert (Seq.length av = n);
  let hd0 = Seq.create 1 false in
  let hd1 = Seq.create 1 true in
  let nav = to_vec (lognot #n a) in
  let eav = Seq.append hd1 av in
  append_lemma #1 #n hd1 av;
  append_lemma #1 #n hd0 nav;
  let nav = BitVector.lognot_vec #n av in
  let neav_r = BitVector.lognot_vec #(n+1) eav in
  let neav_l = Seq.append hd0 nav in
  Seq.Base.lemma_eq_elim neav_l neav_r

#push-options "--z3rlimit 60"
let rec lemma_lognot_value_mod #n a =
    if n = 1 then () else
    begin
      assert (-pow2 n <= (-(a+1)) && -(a+1) < 0);

      let av = to_vec a in
      let hd = from_vec #1 (Seq.slice (to_vec a) 0 1) in
      let tl = from_vec #(n-1) (Seq.slice (to_vec a) 1 n) in

      assert (hd = 0 || hd = 1);
      let hdpow = op_Multiply hd (pow2 (n-1)) in

      from_vec_propriety (to_vec a) 1;
      assert (from_vec av = (op_Multiply
                              (from_vec #1     (Seq.slice av 0 1)) (pow2 (n-1))) +
                              (from_vec #(n-1) (Seq.slice av 1 n)));

      let ntl = lognot tl in
      lemma_lognot_value_mod #(n-1) tl;
      assert (ntl = pow2 (n-1) - tl - 1);

      assert (a = hdpow + tl);
      assert (lognot a = lognot #n (hdpow + tl));
      assert (tl < pow2 (n-1));
      if hdpow = 0 then
      begin
        assert (lognot a = lognot #n tl);
        lemma_lognot_zero_ext #(n-1) tl;
        lemma_zero_extend tl
      end
      else
      begin
        lemma_lognot_one_ext #(n-1) tl;
        lemma_one_extend tl
      end
    end
#pop-options

let lemma_lognot_value_zero #n a =
  let p = pow2 n in
  calc (==) {
    sub_mod (sub_mod 0 a) 1;
    == { }
    sub_mod ((0 - a) % p) 1;
    == { }
    ((0 - a) % p - 1) % p;
    == { }
    (0 % p - 1) % p;
    == { modulo_lemma 0 p }
    (0 - 1) % p;
    == { lemma_mod_sub_0 p }
    p - 1;
    == { }
    p - 0 - 1;
    == { lemma_lognot_value_mod a }
    lognot a;
  }
#pop-options

#push-options "--z3rlimit 150"
private
val lemma_mod_variation: #n:pos -> a:uint_t n ->
  Lemma (a <> 0 ==> ((-a) % pow2 n) - 1 % pow2 n = (((-a) % pow2 n) - 1) % pow2 n)
let lemma_mod_variation #n a = assert (pow2 n =!= 0)
#pop-options

let lemma_one_mod_pow2 #n = ()

#push-options "--z3rlimit 50"
private
val lemma_lognot_value_variation: #n:pos -> a:uint_t n{a <> 0} ->
  Lemma (lognot a = (-a) % pow2 n - 1 % pow2 n)
let lemma_lognot_value_variation #n a =
  let p = pow2 n in
  calc (==) {
    lognot a <: int;
    == { lemma_lognot_value_mod a }
    p - a - 1;
    == { FStar.Math.Lemmas.modulo_lemma a p }
    p - (a % p) - 1;
    == { FStar.Math.Lemmas.modulo_lemma 1 p }
    (p - (a % p)) - (1 % p);
    == { FStar.Math.Lemmas.lemma_mod_sub_1 a p }
    (-a) % p - 1 % p;
  }
#pop-options

let lemma_lognot_value_nonzero #n a =
  let p = pow2 n in
  lemma_lognot_value_variation #n a;
  assert (lognot a = (-a) % (pow2 n) - 1 % (pow2 n));
  assert (sub_mod (sub_mod 0 a) 1 = (((0 - a) % p) - 1) % p);
  lemma_mod_variation #n a;
  assert (((-a) % p) - 1 % p = (((-a) % p) - 1) % p);
  assert ((-a) % p - 1 % p = (((0 - a) % p) - 1) % p)

let lemma_lognot_value #n a =
  if a = 0 then lemma_lognot_value_zero a
  else lemma_lognot_value_nonzero a

let lemma_minus_eq_zero_sub #n a =
  let na = lognot a in
  let ma = minus a in
  assert (sub_mod ma 1 = sub_mod (add_mod na 1) 1);
  lemma_sub_add_cancel na 1;
  assert (sub_mod ma 1 = na);
  lemma_lognot_value #n a;
  assert (na = sub_mod (sub_mod 0 a) 1);
  assert (ma = add_mod (sub_mod (sub_mod 0 a) 1) 1);
  lemma_add_sub_cancel (sub_mod 0 a) 1
