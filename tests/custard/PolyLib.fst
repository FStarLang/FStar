module PolyLib
module U32 = FStar.UInt32

(* Section 116.  [duo U32.t] is a type the monomorphizer creates, so no
   extraction request names it; the unit exports it under its name instead,
   and the consumer adopts that declaration rather than emitting a second
   [struct] of the same name. *)
type duo (a:Type) = { left:a; right:a }

let swap (p:duo U32.t) : duo U32.t = { left = p.right; right = p.left }
