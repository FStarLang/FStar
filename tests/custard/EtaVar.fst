module EtaVar

(* Section 30.16.  [consume]'s body is an application of a *parameter*, so
   eta-reduction shortens it to [fun i -> i] -- a definition of arity one
   whose call sites still supply two arguments.  Eta-expansion is what puts
   the argument back, and it read the demand off the body's head, which here
   is not a name at all.  In C that was Error 368, an over-application.

   The abbreviation is [noextract] and unfolds to an arrow, which is what
   makes the reduction fire in the first place. *)

module U32 = FStar.UInt32

noextract
let sig_t (s:list nat) = u:U32.t -> U32.t

let mk ([@@@FStar.Attributes.monomorphize] s:list nat) : sig_t s = fun u -> u

let consume (i:sig_t [1]) (u:U32.t) : U32.t = i u

let main () : U32.t = if U32.(consume (mk [1]) 7ul =^ 7ul) then 0ul else 1ul
