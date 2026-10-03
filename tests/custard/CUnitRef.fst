module CUnitRef
open FStar.All

(* Section 123.  Nothing here is public and no type mentions it, so the one
   [custard_unit] in the unit is in the source and the header does not carry
   the typedef. *)
let get (r : ref unit) : ML unit = !r

let main () : ML UInt32.t =
  let r = alloc () in
  r := ();
  get r;
  0ul
