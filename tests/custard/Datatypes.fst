module Datatypes
open FStar.All
open FStar.IO

type color = | Red | Green | Blue

let name_of (c:color) : string =
  match c with
  | Red -> "red"
  | Green -> "green"
  | Blue -> "blue"

let main () : ML unit =
  print_string (name_of Green);
  print_string "\n"
