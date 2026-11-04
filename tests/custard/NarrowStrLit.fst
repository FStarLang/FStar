module NarrowStrLit
module U32 = FStar.UInt32
open FStar.All

(* Section 98.  The narrow-float #error is emitted when a file mentions the
   16-bit vocabulary, and a mention is an identifier: a program may print
   these names without using the formats -- Custard's own PrintC does, which
   is how extracting the compiler with Cherry tripped over this.  The escaped
   quotes check that the scan stays outside the literal. *)
let main () : ML U32.t =
  let a = "custard_f16 custard_bf16_add" in
  let b = "CUSTARD_F16_LIT say \"CUSTARD_BF16_LIT(0)\"" in
  if a = b then 1ul else 0ul
