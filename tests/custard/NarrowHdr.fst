module NarrowHdr

open FStar.All
module U16 = FStar.UInt16
module U32 = FStar.UInt32

[@@FStar.Attributes.custard_float 16]
assume val t : Type0
assume val add : t -> t -> t
assume val ieee_eq : t -> t -> bool
assume val of_literal : string -> t

(* Section 98.  The 16-bit vocabulary is the program's; see [Narrow.fst]. *)
[@@FStar.Attributes.custard_extern "narrow_stub_bits";
   FStar.Attributes.custard_c_header "Narrow_stubs.h"]
assume val bits : t -> U16.t

(* Section 123.  A type mentioning a narrow float reaches the header, which
   is therefore the file that has to carry the contract: the counterpart of
   [Narrow], where nothing public mentions one and it goes in the source. *)
noeq type pair = { lo : t; hi : t }

let sum (p : pair) : ML t = add p.lo p.hi

let main () : ML U32.t =
  let p = { lo = of_literal "1.5"; hi = of_literal "1.5" } in
  if ieee_eq (sum p) (of_literal "3.0") && bits p.lo = 15872us
  then 0ul else 1ul
