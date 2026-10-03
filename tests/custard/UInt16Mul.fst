module UInt16Mul
module U16 = FStar.UInt16
module I32 = FStar.Int32
open FStar.All

(* Section 115.  [mul_mod] has no overflow precondition, and the C backend
   emitted [(uint16_t)(x * y)]: both operands promote to [int], the
   multiplication is a signed one, and 65535 * 65535 overflows it.  The cast
   that follows is applied to a value the program was never entitled to
   compute.  A UBSan build says so; an optimizing one is entitled to assume
   it cannot happen.

   The operands are widened to [unsigned int] first, where wrapping is
   defined.  The run below checks the value; the CGREP checks that the
   arithmetic is being done where the standard defines it, which is the part
   a non-sanitizing build cannot observe. *)
let product (x:U16.t) (y:U16.t) : U16.t = U16.mul_mod x y

let bump (x:U16.t) : U16.t = U16.add_mod x 1us

let main () : ML I32.t =
  if U16.eq (product 65535us 65535us) 1us
     && U16.eq (product 1000us 100us) 34464us
     && U16.eq (bump 65535us) 0us
  then 0l else 1l
