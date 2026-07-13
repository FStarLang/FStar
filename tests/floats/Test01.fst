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

let test_f32 () : ML unit =
  F32.(
    line "F32.zero"        (to_string zero);
    line "F32.one"         (to_string one);
    line "F32.of_int 3"    (to_string (of_int 3L));
    line "F32.neg 2"       (to_string (sub zero (of_int 2L)));
    line "F32.add 1 2"     (to_string (add one (of_int 2L)));
    line "F32.sub 5 2"     (to_string (sub (of_int 5L) (of_int 2L)));
    line "F32.mul 3 4"     (to_string (mul (of_int 3L) (of_int 4L)));
    line "F32.div 7 2"     (to_string (div (of_int 7L) (of_int 2L)));
    line "F32.div 1 2"     (to_string (div one (of_int 2L)));
    line "F32.div 1 3"     (to_string (div one (of_int 3L)));
    line "F32.lt 0 1"      (string_of_bool (lt zero one));
    line "F32.lt 1 0"      (string_of_bool (lt one zero));
    line "F32.lte 1 1"     (string_of_bool (lte one one));
    line "F32.ieee_eq 1 1" (string_of_bool (ieee_eq one one));
    line "F32.ieee_eq 0 1" (string_of_bool (ieee_eq zero one));
    line "F32.pos_zero"      (to_string (of_literal "0.0"));
    line "F32.neg_zero"      (to_string (of_literal "-0.0"));
    line "F32.ieee_eq +0 -0" (string_of_bool (ieee_eq (of_literal "0.0") (of_literal "-0.0")));
    line "F32.bit_eq +0 -0"  (string_of_bool (bit_eq  (of_literal "0.0") (of_literal "-0.0")));
    line "F32.ieee_eq nan nan" (string_of_bool (ieee_eq (of_literal "nan") (of_literal "nan")));
    line "F32.bit_eq nan nan"  (string_of_bool (bit_eq  (of_literal "nan") (of_literal "nan")))
  )

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
  test_f32 ();
  test_f64 ()

let _ = main ()
