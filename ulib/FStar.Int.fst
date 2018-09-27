module FStar.Int
open FStar.Mul

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
   | _  -> ()

(* NOTE: anything that you fix/update here should be reflected in [FStar.UInt.fst], which is mostly
 * a copy-paste of this module. *)

(* Necessary mathematical functions. Note: should these go into [prims.fst] or something else? *)

// 'flooring' division
let op_Slash (a:int) (b:int{b <> 0}) : Tot int = 
  if (a >= 0 && b < 0) || (a < 0 && b >= 0) then - (abs a / abs b)
  else abs a / abs b

// Euclidian division
let div_eucl (a:int) (b:nonzero) : Tot int =
  if a < 0 then
    if a % b = 0 then -(-a/b) else -(-a/b) -1
  else
    a / b
let op_Slash_Percent = div_eucl

// 'Circular modulo operator : wraps into [-p/2; p/2[
let op_At_Percent (v:int) (p:int{p>0/\ p%2=0}) : Tot int =
  let m = v % p in if m >= p/2 then m - p else m

(* Specs *)
let max_int (n:pos) : Tot int = pow2 (n-1) - 1
let min_int (n:pos) : Tot int = - (pow2 (n-1))

let fits (x:int) (n:pos) : Tot bool = min_int n <= x && x <= max_int n
let size (x:int) (n:pos) : Tot Type0 = b2t(fits x n)

(* Machine integer type *)
type int_t (n:pos) = x:int{size x n}

(* Addition primitives *)
val add: #n:pos -> a:int_t n -> b:int_t n -> Pure (int_t n)
  (requires (size (a + b) n))
  (ensures (fun _ -> True))
let add #n a b =
  a + b

val add_mod: #n:pos -> int_t n -> int_t n -> Tot (int_t n)
let add_mod #n a b =
  (a + b) @% (pow2 n)

(* Subtraction primitives *)
val sub: #n:pos -> a:int_t n -> b:int_t n -> Pure (int_t n)
  (requires (size (a - b) n))
  (ensures (fun _ -> True))
let sub #n a b =
  a - b

val sub_mod: #n:pos -> a:int_t n -> b:int_t n -> Tot (int_t n)
let sub_mod #n a b =
  (a - b) @% (pow2 n)

(* Multiplication primitives *)
val mul: #n:pos -> a:int_t n -> b:int_t n -> Pure (int_t n)
  (requires (size (a * b) n))
  (ensures (fun _ -> True))
let mul #n a b =
  a * b

val mul_mod: #n:pos -> a:int_t n -> b:int_t n -> Tot (int_t n)
let mul_mod #n a b =
  (a * b) @% (pow2 n)

(* Division primitives *)
val div: #n:pos -> a:int_t n -> b:int_t n{b <> 0} -> Pure (int_t n)
  (requires (size (a / b) n))
  (ensures (fun c -> b <> 0 ==> a / b = c))
let div #n a b =
  a / b

(* Modulo primitives *)
// JK: takes time
#set-options "--z3rlimit 25"
val mod: #n:pos -> a:int_t n -> b:int_t n{b <> 0} -> Tot (int_t n)
let mod #n a b = a - ((a/b) * b)

(* Bitwise operators *)
assume val logand: #n:pos -> int_t n -> int_t n -> Tot (int_t n)
assume val logxor: #n:pos -> int_t n -> int_t n -> Tot (int_t n)
assume val logor: #n:pos -> int_t n -> int_t n -> Tot (int_t n)
assume val lognot: #n:pos -> int_t n -> Tot (int_t n)

(* Comparison operators *)
let eq #n (a:int_t n) (b:int_t n) : Tot bool = a = b
let gt #n (a:int_t n) (b:int_t n) : Tot bool = a > b
let gte #n (a:int_t n) (b:int_t n) : Tot bool = a >= b
let lt #n (a:int_t n) (b:int_t n) : Tot bool = a < b
let lte #n (a:int_t n) (b:int_t n) : Tot bool = a <= b

(* Casts *)
val to_int_t: m:pos -> a:int -> Tot (int_t m)
let to_int_t m a = a @% pow2 m

(* Shift operators *)
assume val shift_right: #n:pos -> a:int_t n -> s:nat -> Pure (int_t n)
  (requires True)
  (ensures (fun b -> b = (a /% (pow2 s))))

val shift_left: #n:pos -> a:int_t n -> s:nat -> Tot (int_t n)
let shift_left #n a s = (a * (pow2 s)) @% (pow2 n)
