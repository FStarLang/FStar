module FloatWidth

open FStar.All
module U32 = FStar.UInt32

(* Section 63.1.  A width Custard does not implement.  The point of the test
   is *where* the diagnostic points: error 386 names the attribute, on the
   declaration that carries it, rather than letting the type fall through to
   "no C representation" (368) at the first use, which is a different module
   and names the type instead of the mistake.

   Section 65.  This used to be 16, which Custard now implements; 8 is the
   width that is still a real format and still absent, so the message a
   reviewer asking for one will see is still the one under test. *)

[@@FStar.Attributes.custard_float 8]
assume val t : Type0

assume val of_literal : string -> t
assume val ieee_eq : t -> t -> bool

let main () : ML U32.t =
  if ieee_eq (of_literal "1.5") (of_literal "1.5") then 0ul else 1ul
