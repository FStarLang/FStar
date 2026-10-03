module FloatSpecialKrml

open FStar.All

module F64 = FStar.Float64

(* Section 125.5.  karamel's [EConstant] carries a floating-point literal as
   text and its grammar is the decimal one, so a NaN has no spelling to hand
   it and the crossing is refused.  The direct C backend does accept it, and
   the diagnostic has to say so. *)

let main () : ML FStar.Int32.t =
  if F64.ieee_eq (F64.of_literal "nan") (F64.of_int 0L) then 1l else 0l
