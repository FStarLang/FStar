module CPartialCall

(* Section 26.3: the positive test for the call-arity check.

   A partial application at the *top level* is eta-expanded to full arity
   (section 25), so it never reaches the backend.  A partial application in a
   local binding is not: there is no declaration to give binders to, and the
   value bound is a closure over the argument it did get.  This is the case
   the check exists for, and until now it was emitted as [Probe_band(a)] --
   a call with one operand against a two-parameter prototype the same run had
   written, which is a C compiler's problem to report rather than ours. *)

let band (a: bool) (b: bool) : bool = a && b

let use (a: bool) : bool = let k : bool -> bool = band a in k true

let main () : bool = use true
