module FStar.Int

let op_Star = op_Multiply

(* Necessary mathematical functions *)
// Powers of n
let rec pow2 (x:nat) : Tot pos = if x = 0 then 1 else op_Multiply 2 (pow2 (x-1))
// Absolute value
let abs (x:int) : Tot int = if x >= 0 then x else -x
// 'flooring' division
let op_Slash (a:int) (b:int{b <> 0}) : Tot int = 
  if (a >= 0 && b < 0) || (a < 0 && b >= 0) then - (abs a / abs b)
  else abs a / abs b
// Euclidian division
let div_eucl (a:int) (b:nonzero) : Tot int =  if a < 0 then (if a % b = 0 then -(-a/b) else -(-a/b) -1) else a / b
let op_Slash_Percent = div_eucl
// 'Circular modulo operator : wraps into [-p/2; p/2[
let op_At_Percent (v:int) (p:int{p>0/\ p%2=0}) : Tot int = let m = v % p in if m >= p/2 then m - p else m

(* Specs *)
let max_int (n:pos) : Tot int = pow2 (n-1) - 1
let min_int (n:pos) : Tot int = - (pow2 (n-1))

let fits (x:int) (n:pos) : Tot bool = (min_int n <= x && x <= max_int n)
let size (x:int) (n:pos) : Tot Type0 = b2t(fits x n)
type int_t (n:pos) = x:int{size x n}

(* OxO0, 0x01 and 0xf.....f constants *)
// JK: doesn't work
// let zero (n:pos) : Tot (int_t n) = 0

val zero: n:pos -> Tot (int_t n)
let zero n = 0

val one: n:nat{n > 1} -> Tot (int_t n)
let one n = 1

val ones: n:nat{n > 1} -> Tot (int_t n)
let ones n = -1

(* Increment and decrement *)
val incr: #n:pos -> a:int_t n{a < max_int n} -> Tot (int_t n)
let incr #n a = a + 1
val pred: #n:pos -> a:int_t n{a > min_int n} -> Tot (int_t n)
let pred #n a = a - 1

abstract val incr_underspec: #n:pos -> a:int_t n -> Tot (b:int_t n{a < max_int n ==> b = a + 1})
let incr_underspec #n a = if (a < max_int n) then a + 1 else magic()
abstract val pred_underspec: #n:pos -> a:int_t n -> Tot (b:int_t n{a > min_int n ==> b = a - 1})
let pred_underspec #n a = if (a > min_int n) then a - 1 else magic()

val incr_mod: #n:pos -> a:int_t n -> Tot (int_t n)
let incr_mod #n a = (a + 1) @% (pow2 n)
val pred_mod: #n:pos -> a:int_t n -> Tot (int_t n)
let pred_mod #n a = (a - 1) @% (pow2 n)

(* Addition primitives *)
val add: #n:pos -> a:int_t n -> b:int_t n{size (a + b) n} -> Tot (int_t n)
let add #n a b = a + b

//let add' #n (a:int_t n) (b:int_t n{a + b < pow2 n}) : Tot (int_t n) = a + b
//let add #n a b = a + b

abstract val add_underspec: #n:pos -> a:int_t n -> b:int_t n -> 
  Tot (c:int_t n{size (a+b) n ==> c = a + b})
let add_underspec #n a b = if fits (a+b) n then a + b else magic ()

val add_mod: #n:pos -> int_t n -> int_t n -> Tot (int_t n)
let add_mod #n a b = (a + b) @% (pow2 n)

(* Subtraction primitives *)
val sub: #n:pos -> a:int_t n -> b:int_t n{size (a-b) n} -> Tot (int_t n)
let sub #n a b = a - b

abstract val sub_underspec: #n:pos -> a:int_t n -> b:int_t n -> 
  Tot (c:int_t n{size (a-b) n ==> c = a - b})
let sub_underspec #n a b = if fits (a-b) n then a - b else magic ()

val sub_mod: #n:pos -> a:int_t n -> b:int_t n -> Tot (int_t n)
let sub_mod #n a b = (a - b) @% (pow2 n)

(* Multiplication primitives *)
val mul: #n:pos -> a:int_t n -> b:int_t n{size (a*b) n} -> Tot (int_t n)
let mul #n a b = a * b

abstract val mul_underspec: #n:pos -> a:int_t n -> b:int_t n -> 
  Tot (c:int_t n{size (a * b) n ==> c = a * b})
let mul_underspec #n a b = if (fits (a*b) n) then a * b else magic ()

val mul_mod: #n:pos -> a:int_t n -> b:int_t n -> Tot (int_t n)
let mul_mod #n a b = (a * b) @% (pow2 n)

(* Division primitives *)
assume val div: #n:pos -> a:int_t n -> b:int_t n{b <> 0} -> Tot (c:int_t n{c = a / b})

(* Modulo primitives *)
// JK: takes time
val mod: #n:pos -> a:int_t n -> b:int_t n{b <> 0} -> Tot (int_t n)
let mod #n a b = a - ((a/b) * b)

(* Bitwise operators *)
assume val logand: #n:pos -> int_t n -> int_t n -> Tot (int_t n)
assume val logxor: #n:pos -> int_t n -> int_t n -> Tot (int_t n)
assume val logor: #n:pos -> int_t n -> int_t n -> Tot (int_t n)
assume val lognot: #n:pos -> int_t n -> Tot (int_t n)

(* Comparison operators *)
let eq #n (a:int_t n) (b:int_t n) : Tot bool = (a = b)
let gt #n (a:int_t n) (b:int_t n) : Tot bool = (a > b)
let gte #n (a:int_t n) (b:int_t n) : Tot bool = (a >= b)
let lt #n (a:int_t n) (b:int_t n) : Tot bool = (a < b)
let lte #n (a:int_t n) (b:int_t n) : Tot bool = (a <= b)

(* Casts *)
val to_int_t: m:pos -> a:int -> Tot (int_t m)
let to_int_t m a = a @% pow2 m

(* Shift operators *)
assume val shift_right: #n:pos -> a:int_t n -> s:nat -> Tot (b:int_t n{b = (a /% (pow2 s))})

val shift_left: #n:pos -> a:int_t n -> s:nat -> Tot (int_t n)
let shift_left #n a s = (a * (pow2 s)) @% (pow2 n)
