module CDangle
open FStar.All
module U32 = FStar.UInt32

type col = | R | G | B

(* Section 6.  An [if] with no [else] as the [then] arm of an [if] that has
   one.  The inner statement fits on a line and so would be written unbraced,
   and C's [else] binds to the nearest unmatched [if]: the [else] meant for
   [a] would attach to [b] instead, and [f false true] would fall through
   silently instead of returning 2. *)
let f (a b : bool) : ML U32.t =
  let r = alloc 0ul in
  (if a then (if b then r := 1ul)
   else r := 2ul);
  !r

(* The same shape reached through a match, where the arm that follows is
   written [else if] rather than [else]. *)
let g (x : col) (b : bool) : ML U32.t =
  let r = alloc 0ul in
  (match x with
   | R -> if b then r := 1ul
   | G -> r := 2ul
   | B -> r := 3ul);
  !r

(* A non-zero exit is the failure: the [.dcran] rule runs the program and
   asks for status 0, and [failwith] has no C realization. *)
let main () : ML U32.t =
  let a1 = f true true in
  let a2 = f true false in
  let a3 = f false true in
  let b1 = g R true in
  let b2 = g R false in
  let b2' = g G false in
  let b3 = g B false in
  if a1 = 1ul && a2 = 0ul && a3 = 2ul &&
     b1 = 1ul && b2 = 0ul && b2' = 2ul && b3 = 3ul
  then 0ul else 1ul
