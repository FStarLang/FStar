module FStar.UInt.Types
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

#reset-options "--initial_fuel 1 --max_fuel 1"
let pow2_n #n p = pow2_le_compat (n - 1) p; pow2 p

let __empty = unit
