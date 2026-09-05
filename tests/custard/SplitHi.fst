module SplitHi
open FStar.All
open FStar.IO
open FStar.Attributes
open SplitLo

(* Realized by hand in SplitMid.ml, which itself calls SplitLo. *)
[@@custard_extern "SplitMid.bump"]
assume val bump (x:int) : int

[@@custard_extern "SplitMid.name"]
assume val name (c:color) : string

let main () : ML unit =
  print_string (name (flip Red));
  print_string (string_of_int (bump 40));
  print_string "\n"
