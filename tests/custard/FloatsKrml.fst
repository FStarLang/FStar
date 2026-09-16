module FloatsKrml

open FStar.All

module F32 = FStar.Float32
module F64 = FStar.Float64
module I32 = FStar.Int32

(* Section 38.4.  The same arithmetic through karamel rather than through
   Custard's own C printer.  Every operand here is a variable rather than a
   literal, which is not an accident: see section 38.6. *)

let area (r : F64.t) : F64.t =
  F64.mul (F64.of_literal "3.14159") (F64.mul r r)

let sum32 (a b : F32.t) : F32.t = F32.add a b

(* Section 118.  [of_int] at an exactly-representable argument now folds to a
   literal, so this halving has to take its dividend as a parameter: two
   constant operands is exactly what karamel's folder cannot read. *)
let half (x : F64.t) : F64.t = F64.div x (F64.of_int 2L)

let main () : ML I32.t =
  let r = F64.of_int 2L in
  let a = area r in
  let ok1 = F64.lt (F64.of_literal "12.56") a && F64.lt a (F64.of_literal "12.57") in
  let h = half (F64.of_int 1L) in
  let ok2 = F64.ieee_eq (F64.add h h) (F64.of_int 1L) in
  let one32 = F32.of_int 1L in
  let ok3 = F32.lte one32 (sum32 one32 one32) in
  if ok1 && ok2 && ok3 then 0l else 1l
