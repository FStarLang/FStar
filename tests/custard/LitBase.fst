module LitBase

open FStar.All

module F64 = FStar.Float64
module U32 = FStar.UInt32
module U64 = FStar.UInt64

(* Section 39.  A literal is the number it denotes plus the base it was
   written in, and neither half is redundant.  The value is what the compiler
   reasons about; the base is what the reader of the generated code wrote. *)

let mask : U32.t = 0xfful
let mask_dec : U32.t = 255ul
let big : U64.t = 0xffffffffffffffffuL

(* -0.0 and 0.0 are the same real number and different floats, and dividing by
   them says which: 1/-0.0 is -inf and 1/0.0 is +inf.  That is why section
   39's [float_lit] keeps the sign out of the magnitude, where a canonical
   real would have swallowed it. *)
let neg_zero : F64.t = F64.of_literal "-0.0"

(* Written three ways, denoting one number.  Two of them are also written in
   a form no C compiler minds and the third is what the exact value looks
   like when it is written out in full. *)
let a : F64.t = F64.of_literal "1.5e-3"
let b : F64.t = F64.of_literal "0.0015"
let c : F64.t = F64.of_literal "+15e-4"

(* A base is not part of a value, so a pattern written in one base has to
   match a scrutinee written in another. *)
let classify (x : U32.t) : U32.t =
  match x with
  | 0xfful -> 1ul
  | 255ul -> 2ul
  | _ -> 3ul

let main () : ML U32.t =
  let ok1 = U32.eq mask mask_dec in
  let ok2 = U64.gt big 0uL in
  let one = F64.of_literal "1.0" in
  let ok3 = F64.ieee_eq neg_zero (F64.of_literal "0.0")
            && F64.lt (F64.div one neg_zero) (F64.of_literal "0.0") in
  let ok4 = F64.ieee_eq a b && F64.ieee_eq b c in
  let ok5 = U32.eq (classify 255ul) 1ul in
  if ok1 && ok2 && ok3 && ok4 && ok5 then 0ul else 1ul
