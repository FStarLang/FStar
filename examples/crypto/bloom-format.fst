module Format

open FStar.Seq

type uint = i:int{0 <= i}
type pint = i:int{1 <= i}

type msg (i:pint) = m:seq byte{length m = i}

val max_int : i:pint -> Tot uint
let rec max_int i =
  if i > 1 then
    256 * max_int (i-1)
  else 256

logic type UInt (len:pint) (i:int) = (0 <= i /\ i < max_int len)
type ulint (len:pint) = i:int{UInt len i}
type uint16 = i:int{UInt 2 i}
let uint16_max = (max_int 2) - 1
type uint32 = i:int{UInt 4 i}

assume val ulint_to_bytes: len:pint -> ulint len -> Tot (msg len)
assume val bytes_to_ulint: len:pint -> x:msg len -> Tot (y:ulint len{ulint_to_bytes len y == x})
assume UINT_inj: forall len s0 s1. Seq.Eq (ulint_to_bytes len s0) (ulint_to_bytes len s1) ==> s0==s1

val uint16_to_bytes: uint16 -> Tot (msg 2)
let uint16_to_bytes = ulint_to_bytes 2
let uint32_to_bytes = ulint_to_bytes 4
val bytes_to_uint16: msg 2 -> Tot uint16
let bytes_to_uint16 = bytes_to_ulint 2
let bytes_to_uint32 = bytes_to_ulint 4
