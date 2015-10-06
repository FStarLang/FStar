open Sieve

let _ =
let max = int_of_string (Sys.argv.(1)) in
print_string (String.concat "," (List.map string_of_int ((sieveFull max))))


(*print_int (Sieve.segFault ()) *)

;;