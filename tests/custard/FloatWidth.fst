module FloatWidth

open FStar.All
module U32 = FStar.UInt32

(* Section 63.1.  A width Custard does not implement.  The point of the test
   is *where* the diagnostic points: error 386 names the attribute, on the
   declaration that carries it, rather than letting the type fall through to
   "no C representation" (368) at the first use, which is a different module
   and names the type instead of the mistake.

   16 is the interesting wrong width rather than an absurd one: half
   precision is a real format that Custard does not have yet, so this is the
   message a reviewer asking for it will actually see. *)

[@@FStar.Attributes.custard_float 16]
assume val t : Type0

assume val of_literal : string -> t
assume val ieee_eq : t -> t -> bool

let main () : ML U32.t =
  if ieee_eq (of_literal "1.5") (of_literal "1.5") then 0ul else 1ul
