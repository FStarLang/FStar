module AnyException
open FStar.All
open FStar.IO

(* Section 116.  [data]'s type is dependent, so it is laid out as [any]; the
   pattern below reads it as a [bool] and needs the coercion that the
   [any]-splitting inserts.  Under an exception constructor the splitting had
   no field types to consult and stopped. *)
noeq type pair = | P : b:bool -> data:(if b then bool else unit) -> pair

exception Box of pair

let pick (e:exn) : ML int =
  match e with
  | Box (P true false) -> 1
  | Box (P true true) -> 2
  | _ -> 3

let main () : ML unit =
  print_string (string_of_int (pick (Box (P true false))));
  print_string "\n";
  print_string (string_of_int (pick (Box (P true true))));
  print_string "\n"
