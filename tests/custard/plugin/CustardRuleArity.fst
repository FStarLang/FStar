module CustardRuleArity

(* Section 64.2.  A rule whose declared arity is too small.

   [thrice] retains three arguments; CustardRulePlugin registers a rule for it
   at arity 1.  The rule therefore returns a non-function, and the two
   left-over arguments are applied to it -- which is not a program, and whose
   only symptom used to be the C compiler objecting to a call through a
   [custard_unit] in generated code.

   The shape is not contrived: the trailing unit applications of a Pulse [fn]
   are arguments like any others, so a rule written by counting the parameters
   its author cares about undercounts by exactly this much.

   Extracted for the warning, not for the output; the emitted C is expected
   not to compile and is not compiled. *)

module U32 = FStar.UInt32

assume val thrice (a:U32.t) (b:U32.t) (c:U32.t) : FStar.All.ML U32.t

let main () : FStar.All.ML U32.t = thrice 1ul 2ul 3ul
