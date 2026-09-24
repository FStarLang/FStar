module FsSplitHi

/// Section 122.18.  The downstream half.  Every reference below crosses a
/// file boundary, so each one is the qualified form of something FsSplitLo
/// emitted under its plain identifier; and this module binds [main] itself,
/// which at home is the name the generated entry point would otherwise take.

open FStar.All
open FsSplitLo

let name (c : color) : string =
  match c with
  | Red -> "red"
  | Green -> "green"

let describe (p : pt) : string =
  string_of_int p.px ^ "," ^ string_of_int p.py

let shout (s : string) : ML string =
  try raise (Bad s)
  with
  | Bad t -> t ^ "!"
  | _ -> "other"

let main () : ML unit =
  FStar.IO.print_string (name (flip Red) ^ "\n");
  FStar.IO.print_string (describe origin ^ "\n");
  FStar.IO.print_string (string_of_int (twice add_one 1) ^ "\n");
  FStar.IO.print_string (twice (fun (s : string) -> s ^ ".") "x" ^ "\n");
  FStar.IO.print_string (shout "no" ^ "\n")
