module Part1.Quicksort.Main
module Q = Part1.Quicksort.Generic

//Printing the elements of an integer list, using the FStar.Printf library
let string_of_int_list l =
  Printf.sprintf "[%s]"
    (String.concat "; " (List.Tot.map (Printf.sprintf "%d") l))

//A main program, which sorts a list and prints it before and after
let main () =
  let orig = [42; 17; 256; 94] in
  let sorted = Q.sort ( <= ) orig in
  let msg =
    Printf.sprintf "Original list = %s\nSorted list = %s\n"
      (string_of_int_list orig)
      (string_of_int_list sorted)
  in
  FStar.IO.print_string msg

//Run ``main ()`` when the module loads
#push-options "--warn_error -272"
let _ = main ()
#pop-options


