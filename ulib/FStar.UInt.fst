module FStar.UInt
open FStar.Mul

(* NOTE: anything that you fix/update here should be reflected in [FStar.Int.fst], which is mostly
 * a copy-paste of this module. *)

(* Specs. Note: lacking any type of functors for F*, this is a copy/paste of [FStar.Int.fst], where
 * the relevant bits that changed are:
 * - definition of max and min
 * - use of regular integer modulus instead of wrap-around modulus *)
let max_int (n:pos) : Tot int = pow2 n - 1
let min_int (n:pos) : Tot int = 0

let fits (x:int) (n:pos) : Tot bool = min_int n <= x && x <= max_int n
let size (x:int) (n:pos) : Tot Type0 = b2t(fits x n)

(* Machine integer type *)
type uint_t (n:pos) = x:int{size x n}

(* Constants *)
val zero: n:pos -> Tot (uint_t n)
let zero n = 0
val one: n:pos -> Tot (uint_t n)
let one n = 1
val ones: n:pos -> Tot (uint_t n)
let ones n = max_int n

(* Increment and decrement *)
val incr: #n:pos -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a < max_int n))) (ensures (fun _ -> True))
let incr #n a =
  a + 1
val decr: #n:pos -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a > min_int n))) (ensures (fun _ -> True))
let decr #n a =
  a - 1

abstract val incr_underspec: #n:pos -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a < max_int n)))
  (ensures (fun b -> a + 1 = b))
let incr_underspec #n a =
  if a < max_int n then a + 1 else magic()

abstract val decr_underspec: #n:pos -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a > min_int n)))
  (ensures (fun b -> a - 1 = b))
let decr_underspec #n a =
  if a > min_int n then a - 1 else magic()

val incr_mod: #n:pos -> a:uint_t n -> Tot (uint_t n)
let incr_mod #n a = (a + 1) % (pow2 n)
val decr_mod: #n:pos -> a:uint_t n -> Tot (uint_t n)
let decr_mod #n a = (a - 1) % (pow2 n)

(* Addition primitives *)
val add: #n:pos -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires (size (a + b) n))
  (ensures (fun _ -> True))
let add #n a b =
  a + b

abstract val add_underspec: #n:pos -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a + b) n ==> a + b = c))
let add_underspec #n a b =
  if fits (a+b) n then a + b else magic ()

val add_mod: #n:pos -> uint_t n -> uint_t n -> Tot (uint_t n)
let add_mod #n a b =
  (a + b) % (pow2 n)

(* Subtraction primitives *)
val sub: #n:pos -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires (size (a - b) n))
  (ensures (fun _ -> True))
let sub #n a b =
  a - b

abstract val sub_underspec: #n:pos -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a - b) n ==> a - b = c))
let sub_underspec #n a b =
  if fits (a-b) n then a - b else magic ()

val sub_mod: #n:pos -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let sub_mod #n a b =
  (a - b) % (pow2 n)

(* Multiplication primitives *)
val mul: #n:pos -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires (size (a * b) n))
  (ensures (fun _ -> True))
let mul #n a b =
  a * b

abstract val mul_underspec: #n:pos -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a * b) n ==> a * b = c))
let mul_underspec #n a b =
  if fits (a*b) n then a * b else magic ()

val mul_mod: #n:pos -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let mul_mod #n a b =
  (a * b) % (pow2 n)

(* Division primitives *)
val div: #n:pos -> a:uint_t n -> b:uint_t n{b <> 0} -> Pure (uint_t n)
  (requires (size (a / b) n))
  (ensures (fun c -> b <> 0 ==> a / b = c))
let div #n a b =
  a / b

abstract val div_underspec: #n:pos -> a:uint_t n -> b:uint_t n{b <> 0} -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    (b <> 0 /\ size (a / b) n) ==> a / b = c))
let div_underspec #n a b =
  if fits (a / b) n then a / b else magic ()

(* Modulo primitives *)
// JK: takes time
val mod: #n:pos -> a:uint_t n -> b:uint_t n{b <> 0} -> Tot (uint_t n)
let mod #n a b = a - ((a/b) * b)

(* Bitwise operators *)
assume val logand: #n:pos -> uint_t n -> uint_t n -> Tot (uint_t n)
assume val logxor: #n:pos -> uint_t n -> uint_t n -> Tot (uint_t n)
assume val logor: #n:pos -> uint_t n -> uint_t n -> Tot (uint_t n)
assume val lognot: #n:pos -> uint_t n -> Tot (uint_t n)

(* Comparison operators *)
let eq #n (a:uint_t n) (b:uint_t n) : Tot bool = (a = b)
let gt #n (a:uint_t n) (b:uint_t n) : Tot bool = (a > b)
let gte #n (a:uint_t n) (b:uint_t n) : Tot bool = (a >= b)
let lt #n (a:uint_t n) (b:uint_t n) : Tot bool = (a < b)
let lte #n (a:uint_t n) (b:uint_t n) : Tot bool = (a <= b)

(* JK: bitwise logic should be expressed usint a separate bitvector type *)
(* Bitwise operators lemmas *)
assume val logand_lemma_1: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures ((logand #n a b) = (logand #n b a)))
assume val logand_lemma_2: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures ((logand #n a (zero n)) = 0))
assume val logand_lemma_3: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures ((logand #n a (ones n)) = a))
assume val logand_lemma_4: #n:pos -> a:uint_t n -> m:nat -> b:uint_t n ->
  Lemma (requires (b = pow2 m - 1)) (ensures ((logand #n a b) = a % pow2 m))

assume val logxor_lemma_1: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures ((logxor #n a b) = (logxor #n b a)))
assume val logxor_lemma_2: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures ((logxor #n a (zero n)) = a))
assume val logxor_lemma_3: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures ((logxor #n a (ones n)) = (lognot #n a)))
assume val logxor_lemma_4: n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures ((logxor #n a a) = 0))

assume val logor_lemma_1: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures ((logor #n a b) = (logor #n b a)))
assume val logor_lemma_2: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures ((logor #n a (zero n)) = a))
assume val logor_lemma_3: #n:pos -> a:uint_t n -> 
  Lemma (requires True) (ensures ((logor #n a (ones n)) = (ones n)))

assume val lognot_lemma_1: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures ((lognot #n (lognot #n a)) = a))
assume val lognot_lemma_2: #n:pos -> 
  Lemma (requires True) (ensures ((lognot #n (zero n)) = (ones n)))

(* Casts *)
val to_uint_t: m:pos -> a:int -> Tot (uint_t m)
let to_uint_t m a = a % pow2 m

(* Shift operators *)
assume val shift_right: #n:pos -> a:uint_t n -> s:nat -> Pure (uint_t n)
  (requires True)
  (ensures (fun b -> b = a / (pow2 s)))

val shift_left: #n:pos -> a:uint_t n -> s:nat -> Tot (uint_t n)
let shift_left #n a s = (a * (pow2 s)) % pow2 n
