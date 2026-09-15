module NarrowG

open FStar.All
module U16 = FStar.UInt16
module U32 = FStar.UInt32

[@@FStar.Attributes.custard_float 16]
assume val t : Type0
assume val add : t -> t -> t
assume val lt  : t -> t -> bool
assume val ieee_eq : t -> t -> bool
assume val of_literal : string -> t

(* Section 98.  The 16-bit vocabulary is the program's; see [Narrow.fst]. *)
[@@FStar.Attributes.custard_extern "narrow_stub_bits";
   FStar.Attributes.custard_c_header "Narrow_stubs.h"]
assume val bits : t -> U16.t

(* Section 66.  A global at a narrow width: this is the case that needs the
   initializer spelling rather than the expression one. *)
let g : t = of_literal "1.5"

let main () : ML U32.t =
  if ieee_eq (add g g) (of_literal "3.0") && bits g = 15872us
  then 0ul else 1ul
