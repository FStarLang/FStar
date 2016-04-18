module FStar.UInt

let op_Star = op_Multiply

let rec pow2 (x:nat) : Tot pos = if x = 0 then 1 else 2 * (pow2 (x-1))

let max_int (n:nat) : Tot int = pow2 n - 1
let min_int (n:nat) : Tot int = 0

let uSize (x:int) (n:nat) : GTot Type0 = (x >= min_int n /\ x <= max_int n)

(* Machine integer type *)
// JK: note that if used without going through the F* libraries specific submodule that will be 
// realized as a Bigint
type uint (n:nat) = x:int{uSize x n}

(* Constants *)
//let zero n : Tot (uint n) = 0
val zero: n:nat -> Tot (uint n)
let zero n = 0

val one: n:pos -> Tot (uint n)
let one n = 1

val ones: n:pos -> Tot (uint n)
let ones n = pow2 n - 1

(* Increment and decrement *)
val incr: #n:pos -> a:uint n{a < max_int n} -> Tot (uint n)
let incr #n a = a + 1
val pred: #n:pos -> a:uint n{a > min_int n} -> Tot (uint n)
let pred #n a = a - 1

abstract val incr_underspec: #n:pos -> a:uint n -> Tot (b:uint n{a < max_int n ==> b = a + 1})
let incr_underspec #n a = if (a < max_int n) then a + 1 else magic()
abstract val pred_underspec: #n:pos -> a:uint n -> Tot (b:uint n{a > min_int n ==> b = a - 1})
let pred_underspec #n a = if (a > min_int n) then a - 1 else magic()

val incr_mod: #n:pos -> a:uint n -> Tot (uint n)
let incr_mod #n a = (a + 1) % (pow2 n)
val pred_mod: #n:pos -> a:uint n -> Tot (uint n)
let pred_mod #n a = (a - 1) % (pow2 n)

(* Addition primitives *)
val add: #n:nat -> a:uint n -> b:uint n{a + b < pow2 n} -> Tot (uint n)
let add #n a b = a + b

abstract val add_underspec: #n:nat -> a:uint n -> b:uint n -> Tot (c:uint n{a + b < pow2 n ==> c = a + b})
let add_underspec #n a b = if (a + b < pow2 n) then a + b else magic ()

val add_mod: #n:nat -> uint n -> uint n -> Tot (uint n)
let add_mod #n a b = (a + b) % (pow2 n)

(* Subtraction primitives *)
val sub: #n:nat -> a:uint n -> b:uint n{a - b >= 0} -> Tot (uint n)
let sub #n a b = a - b

abstract val sub_underspec: #n:nat -> a:uint n -> b:uint n -> Tot (c:uint n{a - b >= 0 ==> c = a - b})
let sub_underspec #n a b = if (a - b >= 0) then a - b else magic ()

val sub_mod: #n:nat -> a:uint n -> b:uint n -> Tot (uint n)
let sub_mod #n a b = (a - b) % (pow2 n)

(* Multiplication primitives *)
val mul: #n:nat -> a:uint n -> b:uint n{a * b < pow2 n} -> Tot (uint n)
let mul #n a b = a * b

abstract val mul_underspec: #n:nat -> a:uint n -> b:uint n -> Tot (c:uint n{a * b < pow2 n ==> c = a * b})
let mul_underspec #n a b = if (a * b < pow2 n) then a * b else magic ()

val mul_mod: #n:nat -> a:uint n -> b:uint n -> Tot (uint n)
let mul_mod #n a b = (a * b) % (pow2 n)

(* Division primitives *)
assume val div: #n:nat -> a:uint n -> b:uint n{b <> 0} -> Tot (c:uint n{c = a / b})

(* Modulo primitives *)
val mod: #n:nat -> a:uint n -> b:uint n{b <> 0} -> Tot (uint n)
let mod #n a b = a - ((a/b) * b)

(* Comparison operators *)
let eq #n (a:uint n) (b:uint n) : Tot bool = (a = b)
let gt #n (a:uint n) (b:uint n) : Tot bool = (a > b)
let gte #n (a:uint n) (b:uint n) : Tot bool = (a >= b)
let lt #n (a:uint n) (b:uint n) : Tot bool = (a < b)
let lte #n (a:uint n) (b:uint n) : Tot bool = (a <= b)

(* Bitwise operators *)
assume val logand: #n:nat -> uint n -> uint n -> Tot (uint n)
assume val logxor: #n:nat -> uint n -> uint n -> Tot (uint n)
assume val logor: #n:nat -> uint n -> uint n -> Tot (uint n)
assume val lognot: #n:nat -> uint n -> Tot (uint n)

(* JK: bitwise logic should be expressed usint a separate bitvector type *)
(* Bitwise operators lemmas *)
assume val logand_lemma_1: #n:nat -> a:uint n -> b:uint n ->
  Lemma (requires True) (ensures ((logand #n a b) = (logand #n b a)))
assume val logand_lemma_2: #n:nat -> a:uint n -> 
  Lemma (requires True) (ensures ((logand #n a (zero n)) = 0))
assume val logand_lemma_3: #n:pos -> a:uint n -> 
  Lemma (requires True) (ensures ((logand #n a (ones n)) = a))
assume val logand_lemma_4: #n:nat -> a:uint n -> m:nat -> b:uint n ->
  Lemma (requires (b = pow2 m - 1)) (ensures ((logand #n a b) = a % pow2 m))

assume val logxor_lemma_1: #n:nat -> a:uint n -> b:uint n ->
  Lemma (requires True) (ensures ((logxor #n a b) = (logxor #n b a)))
assume val logxor_lemma_2: #n:nat -> a:uint n -> 
  Lemma (requires True) (ensures ((logxor #n a (zero n)) = a))
assume val logxor_lemma_3: #n:pos -> a:uint n -> 
  Lemma (requires True) (ensures ((logxor #n a (ones n)) = (lognot #n a)))
assume val logxor_lemma_4: n:nat -> a:uint n -> 
  Lemma (requires True) (ensures ((logxor #n a a) = 0))

assume val logor_lemma_1: #n:nat -> a:uint n -> b:uint n ->
  Lemma (requires True) (ensures ((logor #n a b) = (logor #n b a)))
assume val logor_lemma_2: #n:nat -> a:uint n -> 
  Lemma (requires True) (ensures ((logor #n a (zero n)) = a))
assume val logor_lemma_3: #n:pos -> a:uint n -> 
  Lemma (requires True) (ensures ((logor #n a (ones n)) = (ones n)))

assume val lognot_lemma_1: #n:nat -> a:uint n ->
  Lemma (requires True) (ensures ((lognot #n (lognot #n a)) = a))
assume val lognot_lemma_2: #n:pos -> 
  Lemma (requires True) (ensures ((lognot #n (zero n)) = (ones n)))

(* Casts *)
val to_uint: m:nat -> a:int -> Tot (uint m)
let to_uint m a = a % pow2 m

(* Shift operators *)
assume val shift_right: #n:nat -> a:uint n -> s:nat -> Tot (b:uint n{b = a / (pow2 s)})

val shift_left: #n:nat -> a:uint n -> s:nat -> Tot (uint n)
let shift_left #n a s = (a * (pow2 s)) % pow2 n
