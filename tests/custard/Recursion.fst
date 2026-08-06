module Recursion
open FStar.All
open FStar.IO

let rec fact (n:nat) : nat =
  if n = 0 then 1 else n * fact (n - 1)

let main () : ML unit =
  print_string (string_of_int (fact 5));
  print_string "\n"
