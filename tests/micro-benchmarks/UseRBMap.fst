module UseRBMap

open FStar.RBMap
open FStar.Class.Printable

#push-options "--warn_error -272" //Warning_TopLevelEffect
let _ =
  let s = empty () in
  let s = add 5 "5" s in
  let s = add 1 "1" s in
  let s = add 2 "2" s in
  let s = add 4 "4" s in
  IO.print_string (to_string (mem 0 s) ^ "\n");
  IO.print_string (to_string (mem 1 s) ^ "\n");
  IO.print_string (to_string (mem 2 s) ^ "\n");
  IO.print_string (to_string (mem 3 s) ^ "\n");
  IO.print_string (to_string (mem 4 s) ^ "\n");
  IO.print_string (to_string (mem 5 s) ^ "\n");
  IO.print_string (to_string (lookup 0 s) ^ "\n");
  IO.print_string (to_string (lookup 1 s) ^ "\n");
  IO.print_string (to_string (lookup 2 s) ^ "\n");
  IO.print_string (to_string (lookup 3 s) ^ "\n");
  IO.print_string (to_string (lookup 4 s) ^ "\n");
  IO.print_string (to_string (lookup 5 s) ^ "\n");
  ()
#pop-options