module FStar.UInt.Types

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
  
let max_int (n:nat) : Tot int = pow2 n - 1
let min_int (n:nat) : Tot int = 0

let fits (x:int) (n:nat) : Tot bool = min_int n <= x && x <= max_int n
let size (x:int) (n:nat) : Tot Type0 = b2t(fits x n)

(* Machine integer type *)
let uint_t (n:nat) = x:int{size x n}

(* Constants *)
let zero (n:nat) : Tot (uint_t n) = 0

val pow2_n: #n:pos -> p:nat{p < n} -> Tot (r:uint_t n{r = pow2 p})

let one (n:pos) : Tot (uint_t n) = 1
let ones (n:nat) : Tot (uint_t n) = max_int n
//Just because let cannot be the last thing in the interface..
val __empty : Type0
