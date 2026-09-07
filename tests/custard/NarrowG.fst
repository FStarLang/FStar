module NarrowG

open FStar.All
module U32 = FStar.UInt32

[@@FStar.Attributes.custard_float 16]
assume val t : Type0
assume val add : t -> t -> t
assume val lt  : t -> t -> bool
assume val ieee_eq : t -> t -> bool
assume val of_literal : string -> t

(* Section 66.  A global at a narrow width: this is the case that needs the
   initializer spelling rather than the expression one. *)
let g : t = of_literal "1.5"

let main () : ML U32.t =
  if ieee_eq (add g g) (of_literal "3.0") then 0ul else 1ul
