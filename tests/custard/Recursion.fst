module Recursion
open FStar.All
open FStar.IO

let rec fact (n:nat) : nat =
  if n = 0 then 1 else n * fact (n - 1)

(* Integer literal *patterns*.  OCaml has none -- neither [Prims.int], which
   is a [Z.t], nor a machine integer, whose literal is a call to [uint_to_t] --
   so these have to come out as a variable plus a [when] guard. *)
let rec fib (n:nat) : nat =
  match n with
  | 0 -> 0
  | 1 -> 1
  | _ -> fib (n - 1) + fib (n - 2)

let classify (x:FStar.UInt32.t) : int =
  match x with
  | 0ul -> 100
  | 7ul -> 101
  | _ -> 102

let main () : ML unit =
  print_string (string_of_int (fact 5));
  print_string " ";
  print_string (string_of_int (fib 10));
  print_string " ";
  print_string (string_of_int (classify 0ul));
  print_string (string_of_int (classify 7ul));
  print_string (string_of_int (classify 9ul));
  print_string "\n"
