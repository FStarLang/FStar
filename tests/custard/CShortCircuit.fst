module CShortCircuit
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All

(* Section 115.  {!ShortCircuit} asserts that the connectives survive pass 1;
   this asserts that the C backend still emits them as connectives.  [&&] and
   [||] do not evaluate their right operand unless the left one fails to
   decide, and F* code relies on that: the guard below is the only thing that
   keeps the division from dividing by zero.  The backend hoisted the
   operand's statements ahead of the whole expression -- correct for every
   operand position but this one -- and the division ran whatever the guard
   said.

   The assertion is the run: [safe 0ul true] divides by zero if the operand
   is evaluated, and that is a trap rather than a wrong answer. *)
let safe (x:U32.t) (b:bool) : bool =
  U32.eq x 0ul ||
  (if b then U32.gt (U32.div 100ul x) 5ul else false)

(* The same shape under [&&], whose delayed branch is the other one. *)
let safe_and (x:U32.t) (b:bool) : bool =
  not (U32.eq x 0ul) &&
  (if b then U32.gt (U32.div 100ul x) 5ul else false)

let main () : ML I32.t =
  if safe 0ul true && safe 3ul true && not (safe_and 0ul true)
     && safe_and 3ul true
  then 0l else 1l
