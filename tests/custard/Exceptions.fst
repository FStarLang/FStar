module Exceptions
open FStar.All
open FStar.IO

(* Section 8.5: an F* [exception] is a constructor of the single extensible
   [Prims.exn], so it is a declaration of its own rather than part of one.
   [try_with] is the only way to write a handler -- F* has no [try] syntax --
   and the handler does its own matching on the value. *)

exception Empty
exception Bad of string & int

let check (n:int) : ML int =
  if n < 0 then raise (Bad ("negative", n))
  else if n = 0 then raise Empty
  else n

let run (n:int) : ML string =
  try_with (fun () -> string_of_int (check n))
           (fun e -> match e with
                     | Empty -> "empty"
                     | Bad (s, k) -> s ^ string_of_int k
                     | _ -> "other")

let main () : ML unit =
  print_string (run 7); print_string " ";
  print_string (run 0); print_string " ";
  print_string (run (-3)); print_string "\n"
