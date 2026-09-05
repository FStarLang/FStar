module FloatLit

open FStar.All

module F64 = FStar.Float64

(* Section 38.  [of_literal]'s argument is pasted into the generated code, so
   it is checked against a decimal grammar first.  "1.0); abort(); (" is not a
   floating-point literal, and the answer is a diagnostic rather than a token
   in someone's C. *)

let main () : ML F64.t = F64.of_literal "1.0); abort(); ("
