module Main
open FStar.All
open FStar.IO

let main () : ML unit =
  print_string (Counter.name ^ " " ^ string_of_int (Counter.double 21) ^ "\n")

#push-options "--warn_error -272"
let _ = main ()
#pop-options
