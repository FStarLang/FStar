module FloatSingle

open FStar.All

module F32 = FStar.Float32

(* Section 38.  OCaml has one floating-point type and it is binary64, so a
   single-precision program compiled to OCaml would silently compute at double
   precision.  Saying so is better than rounding twice. *)

let main () : ML F32.t = F32.add (F32.of_literal "0.1") (F32.of_literal "0.2")
