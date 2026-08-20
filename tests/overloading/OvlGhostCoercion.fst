module OvlGhostCoercion
open FStar.Ghost

(* A [@@coercion] whose source is [erased int] itself, rather than one of the
   types [hide] and [reveal] relate. Overload resolution strips [erased]
   before comparing heads, so it has to consult the coercions in scope on the
   unstripped classification as well, or this coercion is invisible to it. *)
type ghint = | GhInt of int

[@@coercion]
let erased_to_ghint (x : erased int) : GTot ghint = GhInt (reveal x)

let k (x : ghint) : int = GhInt?._0 x
