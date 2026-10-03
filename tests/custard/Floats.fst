module Floats

open FStar.All

module F32 = FStar.Float32
module F64 = FStar.Float64
module U32 = FStar.UInt32

(* Section 38.  FStar.Float32 and FStar.Float64 are opaque in F* -- [new val t]
   with an assumed arithmetic vocabulary -- so nothing here is *proved*: the
   point is that the arithmetic becomes C arithmetic on [float] and [double]
   rather than calls into a support library that does not exist.  The program
   checks its own answers and returns a nonzero exit status if any is wrong. *)

let area (r : F64.t) : F64.t =
  F64.mul (F64.of_literal "3.14159") (F64.mul r r)

(* A literal in scientific notation, and a negative one: both are accepted by
   the grammar of section 38, and both are pasted into the output as written
   rather than reformatted. *)
let tiny : F64.t = F64.of_literal "-1.5e-3"

(* Single precision has to *stay* single precision.  Written without the [f]
   suffix, [0.1f + 0.2f] would be computed at double precision and rounded
   once at the end, and would then not equal [0.3f]. *)
let sum32 (a b : F32.t) : F32.t = F32.add a b

let main () : ML U32.t =
  let r = F64.of_literal "2.0" in
  let a = area r in
  (* 3.14159 * 4 = 12.56636 *)
  let ok1 = F64.lt (F64.of_literal "12.56") a && F64.lt a (F64.of_literal "12.57") in
  (* of_int rounds; at 3 there is nothing to round. *)
  let ok2 = F64.ieee_eq (F64.of_int 3L) (F64.of_literal "3.0") in
  let ok3 = F64.lt tiny (F64.of_literal "0.0") in
  let ok4 = F32.ieee_eq (sum32 (F32.of_literal "1.5") (F32.of_literal "2.25"))
                        (F32.of_literal "3.75") in
  let ok5 = F64.lte (F64.div (F64.of_literal "1.0") (F64.of_literal "4.0"))
                    (F64.of_literal "0.25") in
  if ok1 && ok2 && ok3 && ok4 && ok5 then 0ul else 1ul
