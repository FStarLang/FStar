module EtaRoot

(* Section 30.16a (#4932).  [eta_d] is a root and nothing in the program calls
   it: a caller outside the unit does, with the two arguments of its F*
   signature.  Eta-reduction shortened it to [eta_d g = g], and since no call
   site asks for more, eta-expansion never put [u] back, so the C function
   took one parameter and returned [g] itself.  A root keeps its binders on
   the C backends. *)

module U32 = FStar.UInt32

let eta_d (g: U32.t -> U32.t) (u: U32.t) : U32.t = g u

let main () : U32.t = 0ul
