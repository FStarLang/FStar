module OvlNotPrimary
open OvlPoly
open OvlInt
open OvlBool

(* Scope order here is [OvlBool.f; OvlInt.f; OvlPoly.f], so the candidate
   name resolution would pick on its own -- the "primary" -- is OvlBool's
   [f : bool -> bool].

   Applied to [0] it is eliminated, and *two* candidates survive: OvlInt's
   [f : int -> int], and OvlPoly's [f : 'a -> 'a], which survives because
   its formal has no rigid head and so can never be ruled out.

   The rule is that we then return the first *surviving* candidate. That is
   OvlInt's, and it is deliberately not the primary: when the primary has
   itself been eliminated, "return the first" cannot mean "return the answer
   name resolution would have given". [OvlInt.f] adds one and [OvlPoly.f] is
   the identity, so this pins down which of the two survivors was chosen. *)
let first_survivor_not_primary = assert_norm (f 0 == 1)

(* The counterpart, which is what keeps the extension conservative: when the
   primary is eliminated by the filter but would in fact have checked, it is
   restored. [g] here is OvlBool's [bool -> bool -> bool]; a [bool] argument
   keeps it and nothing surprising happens. *)
let primary_kept : bool = g true false
