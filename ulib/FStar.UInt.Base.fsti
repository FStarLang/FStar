module FStar.UInt.Base
open FStar.UInt.Types
open FStar.Mul

(* Increment and decrement *)
let incr (#n:nat) (a:uint_t n) : Pure (uint_t n)
(requires (a < max_int n)) (ensures (fun _ -> True)) =
  a + 1

let decr (#n:nat) (a:uint_t n) : Pure (uint_t n)
  (requires (a > min_int n)) (ensures (fun _ -> True)) =
  a - 1

let incr_mod (#n:nat) (a:uint_t n) : Tot (uint_t n) = 
  (a + 1) % (pow2 n)

let decr_mod (#n:nat) (a:uint_t n) : Tot (uint_t n) = 
  (a - 1) % (pow2 n)

let add (#n:nat) (a:uint_t n) (b:uint_t n) : Pure (uint_t n)
  (requires (size (a + b) n))
  (ensures (fun _ -> True)) =
  a + b

let add_mod (#n:nat) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) =
  (a + b) % (pow2 n)

(* Subtraction primitives *)
let sub (#n:nat) (a:uint_t n) (b:uint_t n) : Pure (uint_t n)
  (requires (size (a - b) n))
  (ensures (fun _ -> True)) = a - b
  
let sub_mod (#n:nat) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) =
  (a - b) % (pow2 n)
  
(* Multiplication primitives *)
let mul (#n:nat) (a:uint_t n) (b:uint_t n) : Pure (uint_t n)
  (requires (size (a * b) n))
  (ensures (fun _ -> True)) =
  a * b

let mul_mod (#n:nat) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) =
  (a * b) % (pow2 n)
  
val mul_div: #n:nat -> a:uint_t n -> b:uint_t n -> 
  Tot (t:uint_t n{t = ((a * b) / (pow2 n))})

(* Division primitives *)
val div: #n:nat -> a:uint_t n -> b:uint_t n{b <> 0} -> Pure (uint_t n)
  (requires (size (a / b) n))
  (ensures (fun c -> a / b = c))

val div_size: #n:pos -> a:uint_t n -> b:uint_t n{b <> 0} ->
  Lemma (requires (size a n)) (ensures (size (a / b) n))

val udiv: #n:pos -> a:uint_t n -> b:uint_t n{b <> 0} -> Pure (uint_t n)
  (requires (True))
  (ensures (fun c -> a / b = c))

(* Modulo primitives *)
let mod (#n:nat) (a:uint_t n) (b:uint_t n{b<>0}) : Tot (uint_t n) =
  a - ((a/b) * b)

val mod_spec: (#n:nat) -> (a:uint_t n) -> (b:uint_t n{b<>0}) -> 
    Lemma (mod #n a b = a % b)

(* Comparison operators *)
let eq #n (a:uint_t n) (b:uint_t n) : Tot bool = (a = b)
let gt #n (a:uint_t n) (b:uint_t n) : Tot bool = (a > b)
let gte #n (a:uint_t n) (b:uint_t n) : Tot bool = (a >= b)
let lt #n (a:uint_t n) (b:uint_t n) : Tot bool = (a < b)
let lte #n (a:uint_t n) (b:uint_t n) : Tot bool = (a <= b)

(* Casts *)
let to_uint_t (m:nat) (a:int) : Tot (uint_t m) = a % pow2 m

val incr_underspec: #n:nat -> a:uint_t n -> Pure (uint_t n)
  (requires (a < max_int n))
  (ensures (fun b -> a + 1 = b))

val decr_underspec: #n:nat -> a:uint_t n -> Pure (uint_t n)
  (requires (a > min_int n))
  (ensures (fun b -> a - 1 = b))

val add_underspec: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a + b) n ==> a + b = c))


val sub_underspec: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a - b) n ==> a - b = c))

val mul_underspec: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a * b) n ==> a * b = c))

val div_underspec: #n:nat -> a:uint_t n -> b:uint_t n{b <> 0} -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    (size (a / b) n) ==> a / b = c))
