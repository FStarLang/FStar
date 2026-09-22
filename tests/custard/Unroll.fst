module Unroll
open FStar.All
open FStar.IO
open FStar.Attributes

(* Section 3: a term binder marked [@@@monomorphize] is specialized on, so this
   loop is fully unrolled at extraction time. *)
let rec loop ([@@@monomorphize] n:nat) (f:unit -> ML unit) : ML unit =
  if n > 0 then (f (); loop (n - 1) f)

let main () : ML unit =
  loop 3 (fun _ -> print_string "x");
  print_string "\n"
