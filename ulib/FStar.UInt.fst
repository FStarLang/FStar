module FStar.UInt

open FStar.Mul
open FStar.BitVector
open FStar.Math.Lemmas

val pow2_values: x:nat -> Lemma
  (requires True)
  (ensures (let p = pow2 x in
   match x with
   | 0  -> p=1
   | 1  -> p=2
   | 8  -> p=256
   | 16 -> p=65536
   | 31 -> p=2147483648
   | 32 -> p=4294967296
   | 63 -> p=9223372036854775808
   | 64 -> p=18446744073709551616
   | 128 -> p=0x100000000000000000000000000000000
   | _  -> True))
  [SMTPat (pow2 x)]
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

(* NOTE: anything that you fix/update here should be reflected in [FStar.Int.fst], which is mostly
 * a copy-paste of this module. *)

(* Specs. Note: lacking any type of functors for F*, this is a copy/paste of [FStar.Int.fst], where
 * the relevant bits that changed are:
 * - definition of max and min
 * - use of regular integer modulus instead of wrap-around modulus *)

#reset-options "--initial_fuel 0 --max_fuel 0"

let max_int (n:nat) : Tot int = pow2 n - 1
let min_int (n:nat) : Tot int = 0

let fits (x:int) (n:nat) : Tot bool = min_int n <= x && x <= max_int n
let size (x:int) (n:nat) : Tot Type0 = b2t(fits x n)

(* Machine integer type *)
type uint_t (n:nat) = x:int{size x n}

(* Constants *)
val zero: n:nat -> Tot (uint_t n)
let zero n = 0

#reset-options "--initial_fuel 1 --max_fuel 1"

val pow2_n: #n:pos -> p:nat{p < n} -> Tot (uint_t n)
let pow2_n #n p = pow2_le_compat (n - 1) p; pow2 p

val one: n:pos -> Tot (uint_t n)
let one n = 1

#reset-options "--initial_fuel 0 --max_fuel 0"

val ones: n:nat -> Tot (uint_t n)
let ones n = max_int n

(* Increment and decrement *)
val incr: #n:nat -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a < max_int n))) (ensures (fun _ -> True))
let incr #n a =
  a + 1
val decr: #n:nat -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a > min_int n))) (ensures (fun _ -> True))
let decr #n a =
  a - 1

abstract val incr_underspec: #n:nat -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a < max_int n)))
  (ensures (fun b -> a + 1 = b))
let incr_underspec #n a =
  if a < max_int n then a + 1 else magic()

abstract val decr_underspec: #n:nat -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a > min_int n)))
  (ensures (fun b -> a - 1 = b))
let decr_underspec #n a =
  if a > min_int n then a - 1 else magic()

val incr_mod: #n:nat -> a:uint_t n -> Tot (uint_t n)
let incr_mod #n a = (a + 1) % (pow2 n)
val decr_mod: #n:nat -> a:uint_t n -> Tot (uint_t n)
let decr_mod #n a = (a - 1) % (pow2 n)

(* Addition primitives *)
val add: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires (size (a + b) n))
  (ensures (fun _ -> True))
let add #n a b =
  a + b

abstract val add_underspec: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a + b) n ==> a + b = c))
let add_underspec #n a b =
  if fits (a+b) n then a + b else magic ()

val add_mod: #n:nat -> uint_t n -> uint_t n -> Tot (uint_t n)
let add_mod #n a b =
  (a + b) % (pow2 n)

(* Subtraction primitives *)
val sub: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires (size (a - b) n))
  (ensures (fun _ -> True))
let sub #n a b =
  a - b

abstract val sub_underspec: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a - b) n ==> a - b = c))
let sub_underspec #n a b =
  if fits (a-b) n then a - b else magic ()

val sub_mod: #n:nat -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let sub_mod #n a b =
  (a - b) % (pow2 n)

(* Multiplication primitives *)
val mul: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires (size (a * b) n))
  (ensures (fun _ -> True))
let mul #n a b =
  a * b

abstract val mul_underspec: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a * b) n ==> a * b = c))
let mul_underspec #n a b =
  if fits (a*b) n then a * b else magic ()

val mul_mod: #n:nat -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let mul_mod #n a b =
  (a * b) % (pow2 n)

val mul_div: #n:nat -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"
let mul_div #n a b =
  FStar.Math.Lemmas.lemma_mult_lt_sqr a b (pow2 n);
  (a * b) / (pow2 n)

#reset-options "--max_fuel 0 --max_ifuel 0"
(* Division primitives *)
val div: #n:nat -> a:uint_t n -> b:uint_t n{b <> 0} -> Pure (uint_t n)
  (requires (size (a / b) n))
  (ensures (fun c -> b <> 0 ==> a / b = c))
let div #n a b =
  a / b

abstract val div_underspec: #n:nat -> a:uint_t n -> b:uint_t n{b <> 0} -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    (b <> 0 /\ size (a / b) n) ==> a / b = c))
let div_underspec #n a b =
  if fits (a / b) n then a / b else magic ()

(* Modulo primitives *)
val mod: #n:nat -> a:uint_t n -> b:uint_t n{b <> 0} -> Tot (uint_t n)
let mod #n a b = a - ((a/b) * b)

(* Comparison operators *)
let eq #n (a:uint_t n) (b:uint_t n) : Tot bool = (a = b)
let gt #n (a:uint_t n) (b:uint_t n) : Tot bool = (a > b)
let gte #n (a:uint_t n) (b:uint_t n) : Tot bool = (a >= b)
let lt #n (a:uint_t n) (b:uint_t n) : Tot bool = (a < b)
let lte #n (a:uint_t n) (b:uint_t n) : Tot bool = (a <= b)

(* Casts *)
val to_uint_t: m:nat -> a:int -> Tot (uint_t m)
let to_uint_t m a = a % pow2 m

open FStar.Seq

(* WARNING: Mind the big endian vs little endian definition *)

#reset-options "--initial_fuel 1 --max_fuel 1"

(* Casts *)
val to_vec: #n:nat -> num:uint_t n -> Tot (bv_t n)
let rec to_vec #n num =
  if n = 0 then Seq.createEmpty #bool
  else Seq.append (to_vec #(n - 1) (num / 2)) (Seq.create 1 (num % 2 = 1))

val from_vec: #n:nat -> vec:bv_t n -> Tot (uint_t n)
let rec from_vec #n vec =
  if n = 0 then 0
  else 2 * from_vec #(n - 1) (slice vec 0 (n - 1)) + (if index vec (n - 1) then 1 else 0)

val to_vec_lemma_1: #n:nat -> a:uint_t n -> b:uint_t n ->
  Lemma (requires a = b) (ensures equal (to_vec a) (to_vec b))
let to_vec_lemma_1 #n a b = ()

val to_vec_lemma_2: #n:nat -> a:uint_t n -> b:uint_t n ->
  Lemma (requires equal (to_vec a) (to_vec b)) (ensures a = b)
let rec to_vec_lemma_2 #n a b =
  if n = 0 then () else begin
    assert(equal (slice (to_vec b) 0 (n - 1)) (to_vec #(n - 1) (b / 2)));
    assert(equal (slice (to_vec a) 0 (n - 1)) (to_vec #(n - 1) (a / 2)));
    to_vec_lemma_2 #(n - 1) (a / 2) (b / 2);
    assert(a % 2 = (if index (to_vec a) (n - 1) then 1 else 0));
    assert(b % 2 = (if index (to_vec b) (n - 1) then 1 else 0));
    assert(a % 2 = b % 2)
  end

val inverse_aux: #n:nat -> vec:bv_t n -> i:nat{i < n} ->
  Lemma (requires True) (ensures index vec i = index (to_vec (from_vec vec)) i)
        [SMTPat (index (to_vec (from_vec vec)) i)]
let rec inverse_aux #n vec i = 
  if i = n - 1 then assert((from_vec vec) % 2 = (if index vec (n - 1) then 1 else 0)) else inverse_aux #(n - 1) (slice vec 0 (n - 1)) i

val inverse_vec_lemma: #n:nat -> vec:bv_t n ->
  Lemma (requires True) (ensures equal vec (to_vec (from_vec vec)))
        [SMTPat (to_vec (from_vec vec))]
let inverse_vec_lemma #n vec = ()

val inverse_num_lemma: #n:nat -> num:uint_t n ->
  Lemma (requires True) (ensures num = from_vec (to_vec num))
        [SMTPat (from_vec (to_vec num))]
let inverse_num_lemma #n num = to_vec_lemma_2 #n num (from_vec (to_vec num))

val from_vec_lemma_1: #n:nat -> a:bv_t n -> b:bv_t n ->
  Lemma (requires equal a b) (ensures from_vec a = from_vec b)
let from_vec_lemma_1 #n a b = ()

val from_vec_lemma_2: #n:nat -> a:bv_t n -> b:bv_t n ->
  Lemma (requires from_vec a = from_vec b) (ensures equal a b)
let from_vec_lemma_2 #n a b = inverse_vec_lemma a; inverse_vec_lemma b


open FStar.Math.Lemmas

#set-options "--initial_fuel 0 --max_fuel 0"

val from_vec_aux: #n:nat -> a:bv_t n -> s1:nat{s1 < n} -> s2:nat{s2 < s1} ->
  Lemma (requires True)
        (ensures (from_vec #s2 (slice a 0 s2)) * pow2 (n - s2) + (from_vec #(s1 - s2) (slice a s2 s1)) * pow2 (n - s1) + (from_vec #(n - s1) (slice a s1 n)) = ((from_vec #s2 (slice a 0 s2)) * pow2 (s1 - s2) + (from_vec #(s1 - s2) (slice a s2 s1))) * pow2 (n - s1) + (from_vec #(n - s1) (slice a s1 n)))
let from_vec_aux #n a s1 s2 =
  paren_mul_left (from_vec #s2 (slice a 0 s2)) (pow2 (s1 - s2)) (pow2 (n - s1));
  paren_mul_right (from_vec #s2 (slice a 0 s2)) (pow2 (s1 - s2)) (pow2 (n - s1));
  pow2_plus (s1 - s2) (n - s1)

#set-options "--initial_fuel 0 --max_fuel 0"

val seq_slice_lemma: #n:nat -> a:bv_t n -> s1:nat{s1 < n} -> t1:nat{t1 >= s1 && t1 <= n} -> s2:nat{s2 < t1 - s1} -> t2:nat{t2 >= s2 && t2 <= t1 - s1} ->
  Lemma (equal (slice (slice a s1 t1) s2 t2) (slice a (s1 + s2) (s1 + t2)))
let seq_slice_lemma #n a s1 t1 s2 t2 = ()

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

val from_vec_propriety: #n:pos -> a:bv_t n -> s:nat{s < n} ->
  Lemma (requires True)
        (ensures from_vec a = (from_vec #s (slice a 0 s)) * pow2 (n - s) + from_vec #(n - s) (slice a s n))
	(decreases (n - s))
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

#reset-options "--initial_fuel 0 --max_fuel 0"

val append_lemma: #n:pos -> #m:pos -> a:bv_t n -> b:bv_t m ->
  Lemma (from_vec #(n + m) (append a b) = (from_vec #n a) * pow2 m + (from_vec #m b))
let append_lemma #n #m a b =
  assert(equal a (slice (append a b) 0 n));
  assert(equal b (slice (append a b) n (n + m)));
  from_vec_propriety #(n + m) (append a b) n

val slice_left_lemma: #n:pos -> a:bv_t n -> s:pos{s < n} ->
  Lemma (requires True)
        (ensures from_vec #s (slice a 0 s) = (from_vec #n a) / (pow2 (n - s)))
let slice_left_lemma #n a s =
  from_vec_propriety #n a s;
  division_addition_lemma (from_vec #(n - s) (slice a s n)) (pow2 (n - s)) (from_vec #s (slice a 0 s));
  small_division_lemma_1 (from_vec #(n - s) (slice a s n)) (pow2 (n - s))

val slice_right_lemma: #n:pos -> a:bv_t n -> s:pos{s < n} ->
  Lemma (requires True)
        (ensures from_vec #s (slice a (n - s) n) = (from_vec #n a) % (pow2 s))
let slice_right_lemma #n a s =
  from_vec_propriety #n a (n - s);
  modulo_addition_lemma (from_vec #s (slice a (n - s) n)) (pow2 s) (from_vec #(n - s) (slice a 0 (n - s)));
  small_modulo_lemma_1 (from_vec #s (slice a (n - s) n)) (pow2 s)

#set-options "--initial_fuel 1 --max_fuel 1"

(* Relations between constants in BitVector and in UInt. *)
val zero_to_vec_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures index (to_vec (zero n)) i = index (zero_vec #n) i)
        [SMTPat (index (to_vec (zero n)) i)]
let rec zero_to_vec_lemma #n i =
  if i = n - 1 then () else zero_to_vec_lemma #(n - 1) i

val zero_from_vec_lemma: #n:pos ->
  Lemma (requires True) (ensures from_vec (zero_vec #n) = zero n)
        [SMTPat (from_vec (zero_vec #n))]
let zero_from_vec_lemma #n = to_vec_lemma_2 (from_vec (zero_vec #n)) (zero n)

val one_to_vec_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (to_vec (one n)) i = index (elem_vec #n (n - 1)) i)
	[SMTPat (index (to_vec (one n)) i)]
let one_to_vec_lemma #n i =
  if i = n - 1 then () else zero_to_vec_lemma #n i

val pow2_to_vec_lemma: #n:pos -> p:nat{p < n} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (to_vec (pow2_n #n p)) i = index (elem_vec #n (n - p - 1)) i)
	[SMTPat (index (to_vec (pow2_n #n p)) i)]
let rec pow2_to_vec_lemma #n p i =
  if i = n - 1 then () 
  else if p = 0 then one_to_vec_lemma #n i
  else pow2_to_vec_lemma #(n - 1) (p - 1) i

val pow2_from_vec_lemma: #n:pos -> p:nat{p < n} ->
  Lemma (requires True) (ensures from_vec (elem_vec #n p) = pow2_n #n (n - p - 1))
        [SMTPat (from_vec (elem_vec #n p))]
let pow2_from_vec_lemma #n p =
  to_vec_lemma_2 (from_vec (elem_vec #n p)) (pow2_n #n (n - p - 1))

val ones_to_vec_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (to_vec (ones n)) i = index (ones_vec #n) i)
	[SMTPat (index (to_vec (ones n)) i)]
let rec ones_to_vec_lemma #n i =
  if i = n - 1 then () else ones_to_vec_lemma #(n - 1) i

val ones_from_vec_lemma: #n:pos ->
  Lemma (requires True) (ensures from_vec (ones_vec #n) = ones n)
        [SMTPat (from_vec (ones_vec #n))]
let ones_from_vec_lemma #n =
  to_vec_lemma_2 (from_vec (ones_vec #n)) (ones n)


(* (nth a i) returns a boolean indicating the i-th bit of a. *)
val nth: #n:pos -> a:uint_t n -> i:nat{i < n} -> Tot bool
let nth #n a i = index (to_vec #n a) i

val nth_lemma: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires forall (i:nat{i < n}). nth a i = nth b i)
        (ensures a = b)
let nth_lemma #n a b =
  assert(forall (i:nat{i < n}). index (to_vec #n a) i = index (to_vec #n b) i);
  to_vec_lemma_2 a b

(* Lemmas for constants *)
val zero_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures nth (zero n) i = false)
        [SMTPat (nth (zero n) i)]
let rec zero_nth_lemma #n i = ()

val pow2_nth_lemma: #n:pos -> p:nat{p < n} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (i = n - p - 1 ==> nth (pow2_n #n p) i = true) /\
	         (i <> n - p - 1 ==> nth (pow2_n #n p) i = false))
        [SMTPat (nth (pow2_n #n p) i)]
let pow2_nth_lemma #n p i = ()

val one_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (i = n - 1 ==> nth (one n) i = true) /\
	         (i < n - 1 ==> nth (one n) i = false))
        [SMTPat (nth (one n) i)]
let one_nth_lemma #n i = ()

val ones_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures (nth (ones n) i) = true)
        [SMTPat (nth (ones n) i)]
let rec ones_nth_lemma #n i = ()

(* Bitwise operators *)
val logand: #n:pos -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let logand #n a b = from_vec #n (logand_vec #n (to_vec #n a) (to_vec #n b))
val logxor: #n:pos -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let logxor #n a b = from_vec #n (logxor_vec #n (to_vec #n a) (to_vec #n b))
val logor: #n:pos -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let logor #n a b = from_vec #n (logor_vec #n (to_vec #n a) (to_vec #n b))
val lognot: #n:pos -> a:uint_t n  -> Tot (uint_t n)
let lognot #n a = from_vec #n (lognot_vec #n (to_vec #n a))

(* Bitwise operators definitions *)
val logand_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (logand a b) i = (nth a i && nth b i)))
	[SMTPat (nth (logand a b) i)]
let logand_definition #n a b i = ()
val logxor_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (logxor a b) i = (nth a i <> nth b i)))
	[SMTPat (nth (logxor a b) i)]
let logxor_definition #n a b i = ()
val logor_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (logor a b) i = (nth a i || nth b i)))
	[SMTPat (nth (logor a b) i)]
let logor_definition #n a b i = ()
val lognot_definition: #n:pos -> a:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (lognot a) i = not(nth a i)))
	[SMTPat (nth (lognot a) i)]
let lognot_definition #n a i = ()

(* Bitwise operators lemmas *)
(* TODO: lemmas about the relations between different operators *)
(* Bitwise AND operator *)
val logand_commutative: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures (logand #n a b = logand #n b a))
let logand_commutative #n a b = nth_lemma #n (logand #n a b) (logand #n b a)

val logand_associative: #n:pos -> a:uint_t n -> b:uint_t n -> c:uint_t n ->
  Lemma (requires True)
	(ensures (logand #n (logand #n a b) c = logand #n a (logand #n b c)))
let logand_associative #n a b c = nth_lemma #n (logand #n (logand #n a b) c) (logand #n a (logand #n b c))

val logand_self: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures (logand #n a a = a))
let logand_self #n a = nth_lemma #n (logand #n a a) a

val logand_lemma_1: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures (logand #n a (zero n) = zero n))
let logand_lemma_1 #n a = nth_lemma #n (logand #n a (zero n)) (zero n)

val logand_lemma_2: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures (logand #n a (ones n) = a))
let logand_lemma_2 #n a = nth_lemma #n (logand #n a (ones n)) a

(* Bitwise XOR operator *)
val logxor_commutative: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures (logxor #n a b = logxor #n b a))
let logxor_commutative #n a b = nth_lemma #n (logxor #n a b) (logxor #n b a)

val logxor_associative: #n:pos -> a:uint_t n -> b:uint_t n -> c:uint_t n ->
  Lemma (requires True) (ensures (logxor #n (logxor #n a b) c = logxor #n a (logxor #n b c)))
let logxor_associative #n a b c = nth_lemma #n (logxor #n (logxor #n a b) c) (logxor #n a (logxor #n b c))

val logxor_self: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logxor #n a a = zero n))
let logxor_self #n a = nth_lemma #n (logxor #n a a) (zero n)

val logxor_lemma_1: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures (logxor #n a (zero n) = a))
let logxor_lemma_1 #n a = nth_lemma #n (logxor #n a (zero n)) a

val logxor_lemma_2: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures (logxor #n a (ones n) = lognot #n a))
let logxor_lemma_2 #n a = nth_lemma #n (logxor #n a (ones n)) (lognot #n a)

#reset-options "--initial_fuel 0 --max_fuel 0"

private let xor (b:bool) (b':bool) : Tot bool = b <> b'
private let xor_lemma (a:bool) (b:bool) : Lemma
  (requires (True))
  (ensures  (xor (xor a b) b = a))
  [SMTPat (xor (xor a b) b)]
  = ()

val logxor_inv: #n:pos -> a:uint_t n -> b:uint_t n -> Lemma
  (a = logxor #n (logxor #n a b) b)
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

(* Bitwise OR operators *)
val logor_commutative: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures (logor #n a b = logor #n b a))
let logor_commutative #n a b = nth_lemma #n (logor #n a b) (logor #n b a)

val logor_associative: #n:pos -> a:uint_t n -> b:uint_t n -> c:uint_t n ->
  Lemma (requires True)
	(ensures (logor #n (logor #n a b) c = logor #n a (logor #n b c)))
let logor_associative #n a b c = nth_lemma #n (logor #n (logor #n a b) c) (logor #n a (logor #n b c))

val logor_self: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures (logor #n a a = a))
let logor_self #n a = nth_lemma #n (logor #n a a) a

val logor_lemma_1: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logor #n a (zero n) = a))
let logor_lemma_1 #n a = nth_lemma (logor #n a (zero n)) a

val logor_lemma_2: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures (logor #n a (ones n) = ones n))
let logor_lemma_2 #n a = nth_lemma (logor #n a (ones n)) (ones n)

(* Bitwise NOT operator *)
val lognot_self: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (lognot #n (lognot #n a) = a))
let lognot_self #n a = nth_lemma (lognot #n (lognot #n a)) a

val lognot_lemma_1: #n:pos -> 
  Lemma (requires True) (ensures (lognot #n (zero n) = ones n))
let lognot_lemma_1 #n = nth_lemma (lognot #n (zero n)) (ones n)

#set-options "--initial_fuel 1 --max_fuel 1"

(** Used in the next two lemmas *)
private val to_vec_mod_pow2: #n:nat -> a:uint_t n -> m:pos -> i:nat{n - m <= i /\ i < n} ->
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
private val to_vec_lt_pow2: #n:nat -> a:uint_t n -> m:nat -> i:nat{i < n - m} ->
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

(** Used in the next two lemmas *)
private val index_to_vec_ones: #n:pos -> m:nat{m <= n} -> i:nat{i < n} ->
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

val logor_disjoint: #n:pos -> a:uint_t n -> b:uint_t n -> m:pos{m < n} ->
  Lemma (requires (a % pow2 m == 0 /\ b < pow2 m))
        (ensures  (logor #n a b == a + b))
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

val logand_mask: #n:pos -> a:uint_t n -> m:pos{m < n} ->
  Lemma (pow2 m < pow2 n /\ logand #n a (pow2 m - 1) == a % pow2 m)
let logand_mask #n a m =
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
val shift_left: #n:pos -> a:uint_t n -> s:nat -> Tot (uint_t n)
let shift_left #n a s = from_vec (shift_left_vec #n (to_vec #n a) s)
val shift_right: #n:pos -> a:uint_t n -> s:nat -> Tot (uint_t n)
let shift_right #n a s = from_vec (shift_right_vec #n (to_vec #n a) s)

(* Shift operators lemmas *)
val shift_left_lemma_1: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i >= n - s} ->
  Lemma (requires True)
	(ensures (nth (shift_left #n a s) i = false))
	[SMTPat (nth (shift_left #n a s) i)]
let shift_left_lemma_1 #n a s i = ()
val shift_left_lemma_2: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i < n - s} ->
  Lemma (requires True)
        (ensures (nth (shift_left #n a s) i = nth #n a (i + s)))
	[SMTPat (nth (shift_left #n a s) i)]
let shift_left_lemma_2 #n a s i = ()
val shift_right_lemma_1: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i < s} ->
  Lemma (requires True)
	(ensures (nth (shift_right #n a s) i = false))
	[SMTPat (nth (shift_right #n a s) i)]
let shift_right_lemma_1 #n a s i = ()
val shift_right_lemma_2: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i >= s} ->
  Lemma (requires True)
        (ensures (nth (shift_right #n a s) i = nth #n a (i - s)))
	[SMTPat (nth (shift_right #n a s) i)]
let shift_right_lemma_2 #n a s i = ()

(* Lemmas with shift operators and bitwise operators *)
val shift_left_logand_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_left #n (logand #n a b) s = logand #n (shift_left #n a s) (shift_left #n b s)))
let shift_left_logand_lemma #n a b s = nth_lemma (shift_left #n (logand #n a b) s) (logand #n (shift_left #n a s) (shift_left #n b s))

val shift_right_logand_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_right #n (logand #n a b) s = logand #n (shift_right #n a s) (shift_right #n b s)))
let shift_right_logand_lemma #n a b s = nth_lemma (shift_right #n (logand #n a b) s) (logand #n (shift_right #n a s) (shift_right #n b s))

val shift_left_logxor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_left #n (logxor #n a b) s = logxor #n (shift_left #n a s) (shift_left #n b s)))
let shift_left_logxor_lemma #n a b s = nth_lemma (shift_left #n (logxor #n a b) s) (logxor #n (shift_left #n a s) (shift_left #n b s))

val shift_right_logxor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_right #n (logxor #n a b) s = logxor #n (shift_right #n a s) (shift_right #n b s)))
let shift_right_logxor_lemma #n a b s = nth_lemma (shift_right #n (logxor #n a b) s) (logxor #n (shift_right #n a s) (shift_right #n b s))

val shift_left_logor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_left #n (logor #n a b) s = logor #n (shift_left #n a s) (shift_left #n b s)))
let shift_left_logor_lemma #n a b s = nth_lemma (shift_left #n (logor #n a b) s) (logor #n (shift_left #n a s) (shift_left #n b s))

val shift_right_logor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_right #n (logor #n a b) s = logor #n (shift_right #n a s) (shift_right #n b s)))
let shift_right_logor_lemma #n a b s = nth_lemma (shift_right #n (logor #n a b) s) (logor #n (shift_right #n a s) (shift_right #n b s))


(* Lemmas about value after shift operations *)
val shift_left_value_aux_1: #n:pos -> a:uint_t n -> s:nat{s >= n} ->
  Lemma (requires True)
        (ensures shift_left #n a s = (a * pow2 s) % pow2 n)
let shift_left_value_aux_1 #n a s = pow2_multiplication_modulo_lemma_1 a n s

val shift_left_value_aux_2: #n:pos -> a:uint_t n ->
  Lemma (requires True)
        (ensures shift_left #n a 0 = (a * pow2 0) % pow2 n)
let shift_left_value_aux_2 #n a = 
  assert_norm(a * pow2 0 = a);
  small_modulo_lemma_1 a (pow2 n)

val shift_left_value_aux_3: #n:pos -> a:uint_t n -> s:pos{s < n} ->
  Lemma (requires True)
        (ensures shift_left #n a s = (a * pow2 s) % pow2 n)
let shift_left_value_aux_3 #n a s = 
  append_lemma #(n - s) #s (slice (to_vec a) s n) (zero_vec #s);
  slice_right_lemma #n (to_vec a) (n - s);
  pow2_multiplication_modulo_lemma_2 a n s

val shift_left_value_lemma: #n:pos -> a:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures shift_left #n a s = (a * pow2 s) % pow2 n)
	[SMTPat (shift_left #n a s)]
let shift_left_value_lemma #n a s =
  if s >= n then shift_left_value_aux_1 #n a s
  else if s = 0 then shift_left_value_aux_2 #n a
  else shift_left_value_aux_3 #n a s

val shift_right_value_aux_1: #n:pos -> a:uint_t n -> s:nat{s >= n} ->
  Lemma (requires True)
        (ensures shift_right #n a s = a / pow2 s)
let shift_right_value_aux_1 #n a s =
  pow2_le_compat s n;
  small_division_lemma_1 a (pow2 s)

val shift_right_value_aux_2: #n:pos -> a:uint_t n ->
  Lemma (requires True)
        (ensures shift_right #n a 0 = a / pow2 0)
let shift_right_value_aux_2 #n a = assert_norm (pow2 0 == 1)

val shift_right_value_aux_3: #n:pos -> a:uint_t n -> s:pos{s < n} ->
  Lemma (requires True)
        (ensures shift_right #n a s = a / pow2 s)
let shift_right_value_aux_3 #n a s = 
  append_lemma #s #(n - s) (zero_vec #s) (slice (to_vec a) 0 (n - s));
  slice_left_lemma #n (to_vec a) (n - s)

val shift_right_value_lemma: #n:pos -> a:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures shift_right #n a s = a / pow2 s)
	[SMTPat (shift_right #n a s)]
let shift_right_value_lemma #n a s =
  if s >= n then shift_right_value_aux_1 #n a s
  else if s = 0 then shift_right_value_aux_2 #n a
  else shift_right_value_aux_3 #n a s


(* val lemma_pow2_values: n:nat -> Lemma *)
(*   (requires (n <= 64)) *)
(*   (ensures  (pow2 0 = 1 *)
(*     /\ pow2 1 = 2 *)
(*     /\ pow2 2 = 4 *)
(*     /\ pow2 3 = 8 *)
(*     /\ pow2 4 = 16 *)
(*     /\ pow2 5 = 32 *)
(*     /\ pow2 6 = 64 *)
(*     /\ pow2 7 = 128 *)
(*     /\ pow2 8 = 256 *)
(*     /\ pow2 9 = 512 *)
(*     /\ pow2 10 = 1024 *)
(*     /\ pow2 11 = 2048 *)
(*     /\ pow2 12 = 4096 *)
(*     /\ pow2 13 = 8192 *)
(*     /\ pow2 14 = 16384 *)
(*     /\ pow2 15 = 32768 *)
(*     /\ pow2 16 = 65536 *)
(*     /\ pow2 17 = 131072 *)
(*     /\ pow2 18 = 262144 *)
(*     /\ pow2 19 = 524288 *)
(*     /\ pow2 20 = 1048576 *)
(*     /\ pow2 21 = 2097152 *)
(*     /\ pow2 22 = 4194304 *)
(*     /\ pow2 23 = 8388608 *)
(*     /\ pow2 24 = 16777216 *)
(*     /\ pow2 25 = 33554432 *)
(*     /\ pow2 26 = 67108864 *)
(*     /\ pow2 27 = 134217728 *)
(*     /\ pow2 28 = 268435456 *)
(*     /\ pow2 29 = 536870912 *)
(*     /\ pow2 30 = 1073741824 *)
(*     /\ pow2 31 = 2147483648 *)
(*     /\ pow2 32 = 4294967296 *)
(*     /\ pow2 33 = 8589934592 *)
(*     /\ pow2 34 = 17179869184 *)
(*     /\ pow2 35 = 34359738368 *)
(*     /\ pow2 36 = 68719476736 *)
(*     /\ pow2 37 = 137438953472 *)
(*     /\ pow2 38 = 274877906944 *)
(*     /\ pow2 39 = 549755813888 *)
(*     /\ pow2 40 = 1099511627776 *)
(*     /\ pow2 41 = 2199023255552 *)
(*     /\ pow2 42 = 4398046511104 *)
(*     /\ pow2 43 = 8796093022208 *)
(*     /\ pow2 44 = 17592186044416 *)
(*     /\ pow2 45 = 35184372088832 *)
(*     /\ pow2 46 = 70368744177664 *)
(*     /\ pow2 47 = 140737488355328 *)
(*     /\ pow2 48 = 281474976710656 *)
(*     /\ pow2 49 = 562949953421312 *)
(*     /\ pow2 50 = 1125899906842624 *)
(*     /\ pow2 51 = 2251799813685248 *)
(*     /\ pow2 52 = 4503599627370496 *)
(*     /\ pow2 53 = 9007199254740992 *)
(*     /\ pow2 54 = 18014398509481984 *)
(*     /\ pow2 55 = 36028797018963968 *)
(*     /\ pow2 56 = 72057594037927936 *)
(*     /\ pow2 57 = 144115188075855872 *)
(*     /\ pow2 58 = 288230376151711744 *)
(*     /\ pow2 59 = 576460752303423488 *)
(*     /\ pow2 60 = 1152921504606846976 *)
(*     /\ pow2 61 = 2305843009213693952 *)
(*     /\ pow2 62 = 4611686018427387904 *)
(*     /\ pow2 63 = 9223372036854775808 *)
(*     /\ pow2 64 = 18446744073709551616 )) *)
(*     [SMTPat (pow2 n)] *)
(* let lemma_pow2_values n = admit() *)

(* assume Lemma_pow2_values: *)
(*   (pow2 0 = 1 /\ pow2 1 = 2 /\ pow2 2 = 4 /\ pow2 3 = 8 *)
(*     /\ pow2 4 = 16 /\ pow2 5 = 32 /\ pow2 6 = 64 /\ pow2 7 = 128 *)
(*     /\ pow2 8 = 256 /\ pow2 9 = 512 /\ pow2 10 = 1024 /\ pow2 11 = 2048 *)
(*     /\ pow2 12 = 4096 /\ pow2 13 = 8192 /\ pow2 14 = 16384 /\ pow2 15 = 32768 *)
(*     /\ pow2 16 = 65536 /\ pow2 17 = 131072 /\ pow2 18 = 262144 /\ pow2 19 = 524288 *)
(*     /\ pow2 20 = 1048576 /\ pow2 21 = 2097152 /\ pow2 22 = 4194304 /\ pow2 23 = 8388608 *)
(*     /\ pow2 24 = 16777216 /\ pow2 25 = 33554432 /\ pow2 26 = 67108864 /\ pow2 27 = 134217728 *)
(*     /\ pow2 28 = 268435456 /\ pow2 29 = 536870912 /\ pow2 30 = 1073741824 /\ pow2 31 = 2147483648 *)
(*     /\ pow2 32 = 4294967296 /\ pow2 33 = 8589934592 /\ pow2 34 = 17179869184 /\ pow2 35 = 34359738368 *)
(*     /\ pow2 36 = 68719476736 /\ pow2 37 = 137438953472 /\ pow2 38 = 274877906944 /\ pow2 39 = 549755813888 *)
(*     /\ pow2 40 = 1099511627776 /\ pow2 41 = 2199023255552 /\ pow2 42 = 4398046511104 /\ pow2 43 = 8796093022208 *)
(*     /\ pow2 44 = 17592186044416 /\ pow2 45 = 35184372088832 /\ pow2 46 = 70368744177664 /\ pow2 47 = 140737488355328 *)
(*     /\ pow2 48 = 281474976710656 /\ pow2 49 = 562949953421312 /\ pow2 50 = 1125899906842624 /\ pow2 51 = 2251799813685248 *)
(*     /\ pow2 52 = 4503599627370496 /\ pow2 53 = 9007199254740992 /\ pow2 54 = 18014398509481984 /\ pow2 55 = 36028797018963968 *)
(*     /\ pow2 56 = 72057594037927936 /\ pow2 57 = 144115188075855872 /\ pow2 58 = 288230376151711744 /\ pow2 59 = 576460752303423488 *)
(*     /\ pow2 60 = 1152921504606846976 /\ pow2 61 = 2305843009213693952 /\ pow2 62 = 4611686018427387904 /\ pow2 63 = 9223372036854775808 *)
(*     /\ pow2 64 = 18446744073709551616) *)
