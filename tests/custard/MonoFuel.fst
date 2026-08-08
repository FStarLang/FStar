module MonoFuel
open FStar.All
open FStar.IO
open FStar.Attributes

(* Section 3.6: recursion through a monomorphized binder does not terminate,
   and has to be cut off by the specialization budget. *)
let rec spin ([@@@monomorphize] n:nat) : Dv nat = spin (n + 1)

let main () : ML unit = print_string (string_of_int (spin 0))
