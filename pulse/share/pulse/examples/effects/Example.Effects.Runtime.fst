module Example.Effects.Runtime
#lang-pulse

(* The single extraction entry point for the executable regression suite.

   Each component proves its exact observable result in Pulse. This module also
   computes comparisons on the runtime values and returns them to driver.ml,
   so the executable exercises extracted code rather than relying only on erased
   proof assertions. There are five checks, in the order documented below.
   Verification-only helpers and expected-failure declarations are not called. *)

open Pulse.Lib.Pervasives
// C exercises ordinary operations and forwarding; Ex exercises local exceptions;
// N exercises nested routing and a change of handler result type.
module C = Example.Effects.Core
module Ex = Example.Effects.Exception
module N = Example.Effects.Nested

// Run all five observations and prove every runtime comparison is true:
// 1. Core: construction leaves state 0; execution returns 42, writes 2, frames 7.
// 2. Raised: the exception clause returns 42 and recovers the cell at state 2.
// 3. Normal: the return clause preserves result 7 and state 3.
// 4. Nested inner: the outer return clause yields true, with state 2.
// 5. Nested outer: forwarding reaches the outer exception clause, yielding
//    false and state 3.
// Literal branch flags deliberately specialize the current Custard tree shapes.
fn test ()
  returns checks:list bool
  ensures pure (checks == [true; true; true; true; true])
{
  let core = C.test ();
  let raised = Ex.test true;
  let normal = Ex.test false;
  let inner = N.test true;
  let outer = N.test false;
  [core = (0, 42, 2, 7);
   raised = (42, 2);
   normal = (7, 3);
   inner = (true, 2);
   outer = (false, 3)]
}
