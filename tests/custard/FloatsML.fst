module FloatsML

open FStar.All

module F64 = FStar.Float64

(* Section 38.  The same arithmetic on the OCaml backend, where a [Float64] is
   OCaml's own [float] and the operators are OCaml's own.  Nothing is printed
   as a float: [to_string] is realized outside F* and this suite has no
   realization for it, so what is checked is the arithmetic. *)

let main () : ML unit =
  let x = F64.add (F64.of_literal "1.5") (F64.of_literal "2.25") in
  FStar.IO.print_string (string_of_bool (F64.ieee_eq x (F64.of_literal "3.75")));
  FStar.IO.print_string "\n";
  FStar.IO.print_string (string_of_bool (F64.lt (F64.of_int 2L) x));
  FStar.IO.print_string "\n";
  FStar.IO.print_string
    (string_of_bool (F64.ieee_eq (F64.mul x (F64.of_literal "2.0"))
                                 (F64.of_literal "7.5")));
  FStar.IO.print_string "\n"
