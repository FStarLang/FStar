module StringOfExn

open FStar.All
open FStar.Exception { string_of_exn }

exception A

// Top-level effects ok
#set-options "--warn_error -272"

let _ =
  try
    raise A
  with
  | e ->
    IO.print_string (string_of_exn e ^ "\n");
    ()
