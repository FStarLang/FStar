module FloatEq

open FStar.All
module U32 = FStar.UInt32

(* Section 63.2.  A name a float module declares and Custard's vocabulary does
   not recognize becomes an ordinary external.  That is deliberate --
   [FStar.Float32.bit_eq] and [to_string] are meant to be calls into a support
   library, and an opted-in library carries its own axioms besides -- but it
   makes a *misspelling* silent: the symptom is an undefined symbol at link
   time, a whole pipeline away from the cause.

   [eq] is the one name worth catching, because the vocabulary spells IEEE
   equality [ieee_eq] precisely to say which equality is meant.  Warning 387
   is the whole product here. *)

[@@FStar.Attributes.custard_float 32]
assume val t : Type0

assume val eq : t -> t -> bool
assume val of_literal : string -> t

let main () : ML U32.t =
  if eq (of_literal "1.5") (of_literal "1.5") then 0ul else 1ul
