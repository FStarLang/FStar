module Test01

open FStar.All
open FStar.IO

module F32 = FStar.Float32
module F64 = FStar.Float64

let line (label:string) (v:string) : ML unit =
  print_string label;
  print_string " = ";
  print_string v;
  print_newline ()

(* [FStar.Float32] is deliberately absent here.  Custard refuses binary32 on
   the OCaml backend (error 368, section 66.4): OCaml has one float type and it
   is binary64, so a program that computes at binary32 everywhere else would
   quietly compute a different answer here.  The legacy OCaml backend did not
   refuse; it emulated the rounding in a realization, and this test used to
   check that emulation.  Float32 is covered against a native binary32 by
   FloatExtract in this directory, and at run time by tests/custard/Floats.fst.
   Section 126.7. *)

let test_f64 () : ML unit =
  F64.(
    line "F64.zero"        (to_string zero);
    line "F64.one"         (to_string one);
    line "F64.of_int 3"    (to_string (of_int 3L));
    line "F64.neg 2"       (to_string (sub zero (of_int 2L)));
    line "F64.add 1 2"     (to_string (add one (of_int 2L)));
    line "F64.sub 5 2"     (to_string (sub (of_int 5L) (of_int 2L)));
    line "F64.mul 3 4"     (to_string (mul (of_int 3L) (of_int 4L)));
    line "F64.div 7 2"     (to_string (div (of_int 7L) (of_int 2L)));
    line "F64.div 1 2"     (to_string (div one (of_int 2L)));
    line "F64.div 1 3"     (to_string (div one (of_int 3L)));
    line "F64.lt 0 1"      (string_of_bool (lt zero one));
    line "F64.lt 1 0"      (string_of_bool (lt one zero));
    line "F64.lte 1 1"     (string_of_bool (lte one one));
    line "F64.ieee_eq 1 1" (string_of_bool (ieee_eq one one));
    line "F64.ieee_eq 0 1" (string_of_bool (ieee_eq zero one));
    line "F64.pos_zero"      (to_string (of_literal "0.0"));
    line "F64.neg_zero"      (to_string (of_literal "-0.0"));
    line "F64.ieee_eq +0 -0" (string_of_bool (ieee_eq (of_literal "0.0") (of_literal "-0.0")));
    line "F64.bit_eq +0 -0"  (string_of_bool (bit_eq  (of_literal "0.0") (of_literal "-0.0")));
    line "F64.ieee_eq nan nan" (string_of_bool (ieee_eq (of_literal "nan") (of_literal "nan")));
    line "F64.bit_eq nan nan"  (string_of_bool (bit_eq  (of_literal "nan") (of_literal "nan")))
  )

let main () : ML unit =
  test_f64 ()

let _ = main ()
