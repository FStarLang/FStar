module FStar.UInt.Vectors
open FStar.UInt.Types
open FStar.Seq
open FStar.BitVector
open FStar.Mul

#reset-options "--initial_fuel 1 --max_fuel 1"

let rec to_vec (#n:nat) (num:uint_t n) : Tot(bv_t n) =
  if n = 0 then Seq.createEmpty #bool
  else Seq.append (to_vec #(n - 1) (num / 2)) (Seq.create 1 (num % 2 = 1))

let rec from_vec (#n:nat) (vec:bv_t n) : Tot (uint_t n) =
  if n = 0 then 0
  else 2 * from_vec #(n - 1) (slice vec 0 (n - 1)) + (if index vec (n - 1) then 1 else 0)

let to_vec_lemma_1 (#n:nat) (a:uint_t n) (b:uint_t n) :
  Lemma (requires a = b) (ensures equal (to_vec a) (to_vec b)) = ()

let rec to_vec_lemma_2 (#n:nat) (a:uint_t n) (b:uint_t n) :
  Lemma (requires equal (to_vec a) (to_vec b)) (ensures a = b) =
  if n = 0 then () else begin
    assert(equal (slice (to_vec b) 0 (n - 1)) (to_vec #(n - 1) (b / 2)));
    assert(equal (slice (to_vec a) 0 (n - 1)) (to_vec #(n - 1) (a / 2)));
    to_vec_lemma_2 #(n - 1) (a / 2) (b / 2);
    assert(a % 2 = (if index (to_vec a) (n - 1) then 1 else 0));
    assert(b % 2 = (if index (to_vec b) (n - 1) then 1 else 0));
    assert(a % 2 = b % 2)
  end

let rec inverse_aux (#n:nat) (vec:bv_t n) (i:nat{i < n}) :
  Lemma (requires True) (ensures index vec i = index (to_vec (from_vec vec)) i)
        [SMTPat (index (to_vec (from_vec vec)) i)] = 
  if i = n - 1 then assert((from_vec vec) % 2 = (if index vec (n - 1) then 1 else 0)) else inverse_aux #(n - 1) (slice vec 0 (n - 1)) i

let inverse_vec_lemma (#n:nat) (vec:bv_t n) :
  Lemma (requires True) (ensures equal vec (to_vec (from_vec vec)))
        [SMTPat (to_vec (from_vec vec))] = ()
	
let inverse_num_lemma (#n:nat) (num:uint_t n) :
  Lemma (requires True) (ensures num = from_vec (to_vec num))
        [SMTPat (from_vec (to_vec num))] = 
	to_vec_lemma_2 #n num (from_vec (to_vec num))

let from_vec_lemma_1 (#n:nat) (a:bv_t n) (b:bv_t n) :
  Lemma (requires equal a b) (ensures from_vec a = from_vec b) = ()

let from_vec_lemma_2 (#n:nat) (a:bv_t n) (b:bv_t n) :
  Lemma (requires from_vec a = from_vec b) (ensures equal a b) = 
  inverse_vec_lemma a; inverse_vec_lemma b

open FStar.Math.Lemmas

#set-options "--initial_fuel 0 --max_fuel 0"

  let from_vec_aux (#n:nat) (a:bv_t n) (s1:nat{s1 < n}) (s2:nat{s2 < s1}) :
    Lemma (requires True)
          (ensures (from_vec #s2 (slice a 0 s2)) * pow2 (n - s2) + (from_vec #(s1 - s2) (slice a s2 s1)) * pow2 (n - s1) + (from_vec #(n - s1) (slice a s1 n)) = ((from_vec #s2 (slice a 0 s2)) * pow2 (s1 - s2) + (from_vec #(s1 - s2) (slice a s2 s1))) * pow2 (n - s1) + (from_vec #(n - s1) (slice a s1 n))) =
  paren_mul_left (from_vec #s2 (slice a 0 s2)) (pow2 (s1 - s2)) (pow2 (n - s1));
  paren_mul_right (from_vec #s2 (slice a 0 s2)) (pow2 (s1 - s2)) (pow2 (n - s1));
  pow2_plus (s1 - s2) (n - s1)

#set-options "--initial_fuel 0 --max_fuel 0"
let seq_slice_lemma (#n:nat) (a:bv_t n) (s1:nat{s1 < n}) 
  (t1:nat{t1 >= s1 && t1 <= n}) (s2:nat{s2 < t1 - s1}) (t2:nat{t2 >= s2 && t2 <= t1 - s1}) :
  Lemma (equal (slice (slice a s1 t1) s2 t2) (slice a (s1 + s2) (s1 + t2))) 
  = ()

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

let rec from_vec_propriety (#n:pos) (a:bv_t n) (s:nat{s < n}) :
    Lemma (requires True)
          (ensures from_vec a = (from_vec #s (slice a 0 s)) * pow2 (n - s) 
					  + from_vec #(n - s) (slice a s n))
	  (decreases (n - s)) =
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

let append_lemma (#n:pos) (#m:pos) (a:bv_t n) (b:bv_t m) :
  Lemma (from_vec #(n + m) (append a b) = (from_vec #n a) * pow2 m + (from_vec #m b)) =
  assert(equal a (slice (append a b) 0 n));
  assert(equal b (slice (append a b) n (n + m)));
  from_vec_propriety #(n + m) (append a b) n

let slice_left_lemma (#n:pos) (a:bv_t n) (s:pos{s < n}) :
  Lemma (requires True)
        (ensures from_vec #s (slice a 0 s) = (from_vec #n a) / (pow2 (n - s))) =
  from_vec_propriety #n a s;
  division_addition_lemma (from_vec #(n - s) (slice a s n)) (pow2 (n - s)) (from_vec #s (slice a 0 s));
  small_division_lemma_1 (from_vec #(n - s) (slice a s n)) (pow2 (n - s))

let slice_right_lemma (#n:pos) (a:bv_t n) (s:pos{s < n}) :
  Lemma (requires True)
        (ensures from_vec #s (slice a (n - s) n) = (from_vec #n a) % (pow2 s)) =
  from_vec_propriety #n a (n - s);
  modulo_addition_lemma (from_vec #s (slice a (n - s) n)) (pow2 s) (from_vec #(n - s) (slice a 0 (n - s)));
  small_modulo_lemma_1 (from_vec #s (slice a (n - s) n)) (pow2 s)

#set-options "--initial_fuel 1 --max_fuel 1"
let rec zero_to_vec_lemma (#n:pos) (i:nat{i < n}) :
  Lemma (requires True) (ensures index (to_vec (zero n)) i = index (zero_vec #n) i)
        [SMTPat (index (to_vec (zero n)) i)] =
  if i = n - 1 then () else zero_to_vec_lemma #(n - 1) i

let zero_from_vec_lemma (#n:pos) : 
  Lemma (requires True) (ensures from_vec (zero_vec #n) = zero n)
        [SMTPat (from_vec (zero_vec #n))] = 
  to_vec_lemma_2 (from_vec (zero_vec #n)) (zero n)
let one_to_vec_lemma (#n:pos) (i:nat{i < n}) :
  Lemma (requires True)
        (ensures index (to_vec (one n)) i = index (elem_vec #n (n - 1)) i)
	[SMTPat (index (to_vec (one n)) i)] =
  if i = n - 1 then () else zero_to_vec_lemma #n i

let rec pow2_to_vec_lemma (#n:pos) (p:nat{p < n}) (i:nat{i < n}) :
  Lemma (requires True)
        (ensures index (to_vec (pow2_n #n p)) i = index (elem_vec #n (n - p - 1)) i)
	[SMTPat (index (to_vec (pow2_n #n p)) i)] =
  if i = n - 1 then () 
  else if p = 0 then one_to_vec_lemma #n i
  else pow2_to_vec_lemma #(n - 1) (p - 1) i

let pow2_from_vec_lemma (#n:pos) (p:nat{p < n}) :
  Lemma (requires True) (ensures from_vec (elem_vec #n p) = pow2_n #n (n - p - 1))
        [SMTPat (from_vec (elem_vec #n p))] =
  to_vec_lemma_2 (from_vec (elem_vec #n p)) (pow2_n #n (n - p - 1))

let rec ones_to_vec_lemma (#n:pos) (i:nat{i < n}) :
  Lemma (requires True)
        (ensures index (to_vec (ones n)) i = index (ones_vec #n) i)
	[SMTPat (index (to_vec (ones n)) i)] =
  if i = n - 1 then () else ones_to_vec_lemma #(n - 1) i

let ones_from_vec_lemma (#n:pos) :
  Lemma (requires True) (ensures from_vec (ones_vec #n) = ones n)
        [SMTPat (from_vec (ones_vec #n))] =
  to_vec_lemma_2 (from_vec (ones_vec #n)) (ones n)

let nth (#n:pos) (a:uint_t n) (i:nat{i < n}) : Tot bool = index (to_vec #n a) i

let nth_lemma (#n:pos) (a:uint_t n) (b:uint_t n) :
  Lemma (requires forall (i:nat{i < n}). nth a i = nth b i)
        (ensures a = b) =
  assert(forall (i:nat{i < n}). index (to_vec #n a) i = index (to_vec #n b) i);
  to_vec_lemma_2 a b

let rec zero_nth_lemma (#n:pos) (i:nat{i < n}) :
  Lemma (requires True) (ensures nth (zero n) i = false)
        [SMTPat (nth (zero n) i)] = ()

let pow2_nth_lemma (#n:pos) (p:nat{p < n}) (i:nat{i < n}) :
  Lemma (requires True)
        (ensures (i = n - p - 1 ==> nth (pow2_n #n p) i = true) /\
	         (i <> n - p - 1 ==> nth (pow2_n #n p) i = false))
        [SMTPat (nth (pow2_n #n p) i)] = ()

let one_nth_lemma (#n:pos) (i:nat{i < n}) :
  Lemma (requires True)
        (ensures (i = n - 1 ==> nth (one n) i = true) /\
	         (i < n - 1 ==> nth (one n) i = false))
        [SMTPat (nth (one n) i)] = ()
let rec ones_nth_lemma (#n:pos) (i:nat{i < n}) :
  Lemma (requires True) (ensures (nth (ones n) i) = true)
        [SMTPat (nth (ones n) i)] = ()

let logand (#n:pos) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) = 
  from_vec #n (logand_vec #n (to_vec #n a) (to_vec #n b))
let logxor (#n:pos) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) = 
  from_vec #n (logxor_vec #n (to_vec #n a) (to_vec #n b))
let logor (#n:pos) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) = 
  from_vec #n (logor_vec #n (to_vec #n a) (to_vec #n b))
let lognot  (#n:pos) (a:uint_t n) : Tot (uint_t n) = 
  from_vec #n (lognot_vec #n (to_vec #n a))

(* Bitwise operators definitions *)
let logand_definition (#n:pos) (a:uint_t n) (b:uint_t n) (i:nat{i < n}) :
  Lemma (requires True)
	(ensures (nth (logand a b) i = (nth a i && nth b i)))
	[SMTPat (nth (logand a b) i)] = ()
let logxor_definition (#n:pos) (a:uint_t n) (b:uint_t n) (i:nat{i < n}) :
  Lemma (requires True)
	(ensures (nth (logxor a b) i = (nth a i <> nth b i)))
	[SMTPat (nth (logxor a b) i)] = ()
let logor_definition (#n:pos) (a:uint_t n) (b:uint_t n) (i:nat{i < n}) :
  Lemma (requires True)
	(ensures (nth (logor a b) i = (nth a i || nth b i)))
	[SMTPat (nth (logor a b) i)] = ()
let lognot_definition (#n:pos) (a:uint_t n) (i:nat{i < n}) :
  Lemma (requires True)
	(ensures (nth (lognot a) i = not(nth a i)))
	[SMTPat (nth (lognot a) i)] = ()

(* Bitwise operators lemmas *)
(* TODO: lemmas about the relations between different operators *)
(* Bitwise AND operator *)
let logand_commutative (#n:pos) (a:uint_t n) (b:uint_t n) :
  Lemma (requires True) (ensures (logand #n a b = logand #n b a)) = 
  nth_lemma #n (logand #n a b) (logand #n b a)

let logand_associative (#n:pos) (a:uint_t n) (b:uint_t n) (c:uint_t n) :
  Lemma (requires True)
	(ensures (logand #n (logand #n a b) c = logand #n a (logand #n b c))) = 
  nth_lemma #n (logand #n (logand #n a b) c) (logand #n a (logand #n b c))

let logand_self (#n:pos) (a:uint_t n) : 
  Lemma (requires True) (ensures (logand #n a a = a)) = 
  nth_lemma #n (logand #n a a) a

let logand_lemma_1 (#n:pos) (a:uint_t n) : 
  Lemma (requires True) (ensures (logand #n a (zero n) = zero n)) = 
  nth_lemma #n (logand #n a (zero n)) (zero n)

let logand_lemma_2 (#n:pos) (a:uint_t n) : 
  Lemma (requires True) (ensures (logand #n a (ones n) = a)) = 
  nth_lemma #n (logand #n a (ones n)) a

(* subset_vec_le_lemma proves that a subset of bits is numerically smaller or equal. *)
val subset_vec_le_lemma: #n:pos -> a:bv_t n -> b:bv_t n ->
  Lemma (requires is_subset_vec #n a b) (ensures (from_vec a) <= (from_vec b))
let rec subset_vec_le_lemma (#n:pos) (a:bv_t n) (b:bv_t n) :
  Lemma (requires is_subset_vec #n a b) (ensures (from_vec a) <= (from_vec b))
  = match n with
    | 1 -> ()
    | _ -> lemma_slice_subset_vec #n a b 0 (n-1);
          subset_vec_le_lemma #(n-1) (slice a 0 (n-1)) (slice b 0 (n-1))

(* logand_le proves the the result of AND is less than or equal to both arguments. *)
val logand_le: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True)
        (ensures (logand a b) <= a /\ (logand a b) <= b)
let logand_le (#n:pos) (a:uint_t n) (b:uint_t n) :
  Lemma (requires True)
        (ensures (logand a b) <= a /\ (logand a b) <= b) =
  let va = to_vec a in
  let vb = to_vec b in
  let vand = to_vec (logand a b) in
  subset_vec_le_lemma #n vand va;
  subset_vec_le_lemma #n vand vb


(* Bitwise XOR operator *)
let logxor_commutative (#n:pos) (a:uint_t n) (b:uint_t n) :
  Lemma (requires True) (ensures (logxor #n a b = logxor #n b a)) = 
  nth_lemma #n (logxor #n a b) (logxor #n b a)

let logxor_associative (#n:pos) (a:uint_t n) (b:uint_t n) (c:uint_t n) :
  Lemma (requires True) (ensures (logxor #n (logxor #n a b) c = 
  logxor #n a (logxor #n b c))) = 
  nth_lemma #n (logxor #n (logxor #n a b) c) (logxor #n a (logxor #n b c))

let logxor_self (#n:pos) (a:uint_t n) :
  Lemma (requires True) (ensures (logxor #n a a = zero n)) = 
  nth_lemma #n (logxor #n a a) (zero n)

let logxor_lemma_1 (#n:pos) (a:uint_t n) : 
  Lemma (requires True) (ensures (logxor #n a (zero n) = a)) = 
  nth_lemma #n (logxor #n a (zero n)) a

let logxor_lemma_2 (#n:pos) (a:uint_t n) : 
  Lemma (requires True) (ensures (logxor #n a (ones n) = lognot #n a)) = 
  nth_lemma #n (logxor #n a (ones n)) (lognot #n a)

#reset-options "--initial_fuel 0 --max_fuel 0"

private let xor (b:bool) (b':bool) : Tot bool = b <> b'
private let xor_lemma (a:bool) (b:bool) : Lemma
  (requires (True))
  (ensures  (xor (xor a b) b = a))
  [SMTPat (xor (xor a b) b)]
  = ()

let logxor_inv (#n:pos) (a:uint_t n) (b:uint_t n) : Lemma
  (a = logxor #n (logxor #n a b) b) =
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

(* Bitwise OR operators *)
let logor_commutative (#n:pos) (a:uint_t n) (b:uint_t n) :
  Lemma (requires True) (ensures (logor #n a b = logor #n b a)) = 
  nth_lemma #n (logor #n a b) (logor #n b a)

let logor_associative (#n:pos) (a:uint_t n) (b:uint_t n) (c:uint_t n) :
  Lemma (requires True)
	(ensures (logor #n (logor #n a b) c = logor #n a (logor #n b c))) = 
  nth_lemma #n (logor #n (logor #n a b) c) (logor #n a (logor #n b c))

let logor_self (#n:pos) (a:uint_t n) : 
  Lemma (requires True) (ensures (logor #n a a = a)) = 
  nth_lemma #n (logor #n a a) a

let logor_lemma_1 (#n:pos) (a:uint_t n) :
  Lemma (requires True) (ensures (logor #n a (zero n) = a)) = 
  nth_lemma (logor #n a (zero n)) a

let logor_lemma_2 (#n:pos) (a:uint_t n) : 
  Lemma (requires True) (ensures (logor #n a (ones n) = ones n)) = 
  nth_lemma (logor #n a (ones n)) (ones n)

#set-options "--initial_fuel 1 --max_fuel 1"

(* superset_vec_le_lemma proves that a superset of bits is numerically greater than or equal. *)
let rec superset_vec_ge_lemma (#n:pos) (a:bv_t n) (b:bv_t n) :
  Lemma (requires is_superset_vec #n a b)
        (ensures (from_vec a) >= (from_vec b)) = match n with
  | 1 -> ()
  | _ -> lemma_slice_superset_vec #n a b 0 (n-1);
        superset_vec_ge_lemma #(n-1) (slice a 0 (n-1)) (slice b 0 (n-1))

(* logor_ge proves that the result of an OR is greater than or equal to both arguments. *)
let logor_ge (#n:pos) (a:uint_t n) (b:uint_t n) :
  Lemma (requires True)
        (ensures (logor a b) >= a /\ (logor a b) >= b) =
  let va = to_vec a in
  let vb = to_vec b in
  let vor = to_vec (logor a b) in
  superset_vec_ge_lemma #n vor va;
  superset_vec_ge_lemma #n vor vb


(* Bitwise NOT operator *)
let lognot_self (#n:pos) (a:uint_t n) :
  Lemma (requires True) (ensures (lognot #n (lognot #n a) = a)) = 
  nth_lemma (lognot #n (lognot #n a)) a

let lognot_lemma_1 (#n:pos) : 
  Lemma (requires True) (ensures (lognot #n (zero n) = ones n)) = 
  nth_lemma (lognot #n (zero n)) (ones n)

(** Used in the next two lemmas *)
private val to_vec_mod_pow2: (#n:nat) -> (a:uint_t n) -> (m:pos) -> (i:nat{n - m <= i /\ i < n}) ->
  Lemma (requires (a % pow2 m == 0))
        (ensures  (index (to_vec a) i == false))
        [SMTPat (index (to_vec #n a) i); SMTPatT (a % pow2 m == 0)]
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

(** Used in the next two lemmas *)
private val to_vec_lt_pow2: (#n:nat) -> (a:uint_t n) -> (m:nat) -> i:nat{i < n - m} ->
  Lemma (requires (a < pow2 m))
        (ensures  (index (to_vec a) i == false))
        [SMTPat (index (to_vec #n a) i); SMTPatT (a < pow2 m)]
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

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"
(** Used in the next two lemmas *)
private val index_to_vec_ones: (#n:pos) -> (m:nat{m <= n}) -> (i:nat{i < n}) ->
  Lemma (requires True)
        (ensures (pow2 m <= pow2 n /\
          (i < n - m ==> index (to_vec #n (pow2 m - 1)) i == false) /\
          (n - m <= i ==> index (to_vec #n (pow2 m - 1)) i == true)))
        [SMTPat (index (to_vec #n (pow2 m - 1)) i)]
let rec index_to_vec_ones #n m i =
   let a = pow2 m - 1 in
   pow2_le_compat n m;
   if m = 0 then one_to_vec_lemma #n i
   else if m = n then ones_to_vec_lemma #n i
   else if i = n - 1 then ()
   else index_to_vec_ones #(n - 1) (m - 1) i

#reset-options "--initial_fuel 0 --max_fuel 0"

let logor_disjoint (#n:pos) (a:uint_t n) (b:uint_t n) (m:pos{m < n}) :
  Lemma (requires (a % pow2 m == 0 /\ b < pow2 m))
        (ensures  (logor #n a b == a + b)) =
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

let logand_mask (#n:pos) (a:uint_t n) (m:pos{m < n}) :
  Lemma (pow2 m < pow2 n /\ logand #n a (pow2 m - 1) == a % pow2 m) =
  pow2_lt_compat n m;
  Seq.lemma_split (logand_vec (to_vec a) (to_vec (pow2 m - 1))) (n - m);
  Seq.lemma_eq_intro
    (logand_vec (to_vec a) (to_vec (pow2 m - 1)))
    (append (zero_vec #(n - m)) (slice (to_vec a) (n - m) n));
  append_lemma #(n - m) #m (zero_vec #(n - m)) (slice (to_vec a) (n - m) n);
  assert (0 * pow2 m + a % pow2 m == a % pow2 m);
  assert (from_vec #(n - m) (zero_vec #(n - m)) == 0);
  slice_right_lemma #n (to_vec a) m;
  assert (from_vec #m (slice (to_vec a) (n - m) n) == a % pow2 m)


(* Shift operators *)
let shift_left (#n:pos) (a:uint_t n) (s:nat) : Tot (uint_t n) = 
  from_vec (shift_left_vec #n (to_vec #n a) s)
let shift_right (#n:pos) (a:uint_t n) (s:nat) : Tot (uint_t n) = 
  from_vec (shift_right_vec #n (to_vec #n a) s)

(* Shift operators lemmas *)
let shift_left_lemma_1  (#n:pos) (a:uint_t n) (s:nat) (i:nat{i < n && i >= n - s}) :
  Lemma (requires True)
	(ensures (nth (shift_left #n a s) i = false))
	[SMTPat (nth (shift_left #n a s) i)] = ()
let shift_left_lemma_2 (#n:pos) (a:uint_t n) (s:nat) (i:nat{i < n && i < n - s}) :
  Lemma (requires True)
        (ensures (nth (shift_left #n a s) i = nth #n a (i + s)))
	[SMTPat (nth (shift_left #n a s) i)] = ()
let shift_right_lemma_1 (#n:pos) (a:uint_t n) (s:nat) (i:nat{i < n && i < s}) :
  Lemma (requires True)
	(ensures (nth (shift_right #n a s) i = false))
	[SMTPat (nth (shift_right #n a s) i)] = ()
let shift_right_lemma_2 (#n:pos) (a:uint_t n) (s:nat) (i:nat{i < n && i >= s}) :
  Lemma (requires True)
        (ensures (nth (shift_right #n a s) i = nth #n a (i - s)))
	[SMTPat (nth (shift_right #n a s) i)] = ()

(* Lemmas with shift operators and bitwise operators *)
let shift_left_logand_lemma (#n:pos) (a:uint_t n) (b:uint_t n) (s:nat) :
  Lemma (requires True)
        (ensures (shift_left #n (logand #n a b) s = logand #n (shift_left #n a s) (shift_left #n b s))) = 
  nth_lemma (shift_left #n (logand #n a b) s) (logand #n (shift_left #n a s) (shift_left #n b s))

let shift_right_logand_lemma (#n:pos) (a:uint_t n) (b:uint_t n) (s:nat) :
  Lemma (requires True)
        (ensures (shift_right #n (logand #n a b) s = logand #n (shift_right #n a s) (shift_right #n b s))) = 
  nth_lemma (shift_right #n (logand #n a b) s) (logand #n (shift_right #n a s) (shift_right #n b s))

let shift_left_logxor_lemma (#n:pos) (a:uint_t n) (b:uint_t n) (s:nat) :
  Lemma (requires True)
        (ensures (shift_left #n (logxor #n a b) s = logxor #n (shift_left #n a s) (shift_left #n b s))) = 
  nth_lemma (shift_left #n (logxor #n a b) s) (logxor #n (shift_left #n a s) (shift_left #n b s))

let shift_right_logxor_lemma (#n:pos) (a:uint_t n) (b:uint_t n) (s:nat) :
  Lemma (requires True)
        (ensures (shift_right #n (logxor #n a b) s = logxor #n (shift_right #n a s) (shift_right #n b s))) = 
  nth_lemma (shift_right #n (logxor #n a b) s) (logxor #n (shift_right #n a s) (shift_right #n b s))

let shift_left_logor_lemma (#n:pos) (a:uint_t n) (b:uint_t n) (s:nat) :
  Lemma (requires True)
        (ensures (shift_left #n (logor #n a b) s = logor #n (shift_left #n a s) (shift_left #n b s))) = 
  nth_lemma (shift_left #n (logor #n a b) s) (logor #n (shift_left #n a s) (shift_left #n b s))

let shift_right_logor_lemma (#n:pos) (a:uint_t n) (b:uint_t n) (s:nat) :
  Lemma (requires True)
        (ensures (shift_right #n (logor #n a b) s = logor #n (shift_right #n a s) (shift_right #n b s))) = 
  nth_lemma (shift_right #n (logor #n a b) s) (logor #n (shift_right #n a s) (shift_right #n b s))


(* Lemmas about value after shift operations *)
let shift_left_value_aux_1 (#n:pos) (a:uint_t n) (s:nat{s >= n}) :
  Lemma (requires True)
        (ensures shift_left #n a s = (a * pow2 s) % pow2 n) =
  pow2_multiplication_modulo_lemma_1 a n s

let shift_left_value_aux_2 (#n:pos) (a:uint_t n) :
  Lemma (requires True)
        (ensures shift_left #n a 0 = (a * pow2 0) % pow2 n) = 
  assert_norm(a * pow2 0 = a);
  small_modulo_lemma_1 a (pow2 n)

let shift_left_value_aux_3 (#n:pos) (a:uint_t n) (s:pos{s < n}) :
  Lemma (requires True)
        (ensures shift_left #n a s = (a * pow2 s) % pow2 n) = 
  append_lemma #(n - s) #s (slice (to_vec a) s n) (zero_vec #s);
  slice_right_lemma #n (to_vec a) (n - s);
  pow2_multiplication_modulo_lemma_2 a n s

let shift_left_value_lemma (#n:pos) (a:uint_t n) (s:nat) :
  Lemma (requires True)
        (ensures shift_left #n a s = (a * pow2 s) % pow2 n)
	[SMTPat (shift_left #n a s)] =
  if s >= n then shift_left_value_aux_1 #n a s
  else if s = 0 then shift_left_value_aux_2 #n a
  else shift_left_value_aux_3 #n a s

let shift_right_value_aux_1 (#n:pos) (a:uint_t n) (s:nat{s >= n}) :
  Lemma (requires True)
        (ensures shift_right #n a s = a / pow2 s) =
  pow2_le_compat s n;
  small_division_lemma_1 a (pow2 s)

let shift_right_value_aux_2 (#n:pos) (a:uint_t n) :
  Lemma (requires True)
        (ensures shift_right #n a 0 = a / pow2 0) = 
  assert_norm (pow2 0 == 1)

let shift_right_value_aux_3 (#n:pos) (a:uint_t n) (s:pos{s < n}) :
  Lemma (requires True)
        (ensures shift_right #n a s = a / pow2 s) = 
  append_lemma #s #(n - s) (zero_vec #s) (slice (to_vec a) 0 (n - s));
  slice_left_lemma #n (to_vec a) (n - s)

let shift_right_value_lemma (#n:pos) (a:uint_t n) (s:nat) :
  Lemma (requires True)
        (ensures shift_right #n a s = a / pow2 s)
	[SMTPat (shift_right #n a s)] =
  if s >= n then shift_right_value_aux_1 #n a s
  else if s = 0 then shift_right_value_aux_2 #n a
  else shift_right_value_aux_3 #n a s
