module UseRBSet

open FStar.RBSet
open FStar.Class.Printable

#push-options "--warn_error -272" //Warning_TopLevelEffect
let _ =
  let s = empty () in
  let s = add 5 s in
  let s = add 1 s in
  let s = add 2 s in
  let s = add 4 s in
  IO.print_string (to_string (mem 0 s) ^ "\n");
  IO.print_string (to_string (mem 1 s) ^ "\n");
  IO.print_string (to_string (mem 2 s) ^ "\n");
  IO.print_string (to_string (mem 3 s) ^ "\n");
  IO.print_string (to_string (mem 4 s) ^ "\n");
  IO.print_string (to_string (mem 5 s) ^ "\n");
  ()
#pop-options