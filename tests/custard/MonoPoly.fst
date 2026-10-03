module MonoPoly
open FStar.All
open FStar.IO
open FStar.Attributes

(* Section 3.2(b): [m] is a runtime parameter of [h], so it cannot be supplied
   to [g]'s monomorphized binder. *)
let g ([@@@monomorphize] n:nat) : nat = n + 1

let h (m:nat) : nat = g m

let main () : ML unit = print_string (string_of_int (h 3))
