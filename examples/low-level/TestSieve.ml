open Sieve

let _ = 
print_string (String.concat "," (List.map string_of_int ((sieveFull 50))));;
