module FloatHole

(* Section 38.  A Float32 program with no Float32 in any signature.

   [a], [b] and the sum are all local to [main], whose type is [unit -> ML
   U32.t], so nothing the OCaml backend prints as a *type* is ever a float.
   The refusal in [ty] therefore never fires, and before the check moved to
   the literal and the operator this extracted silently and computed at
   binary64.

   That is not a missing feature, it is a different answer.  At binary32 the
   sum is exactly [a], because 1e-8 is far below the ulp of 1.0 at 24 bits of
   significand; at binary64 it is not.  So the C backend returned 0 here and
   the OCaml backend returned 1, from this source, with no diagnostic. *)

open FStar.All
module U32 = FStar.UInt32
module F = FStar.Float32

let main () : ML U32.t =
  let a = F.of_literal "1.0" in
  let b = F.of_literal "0.00000001" in
  if F.ieee_eq (F.add a b) a then 0ul else 1ul
