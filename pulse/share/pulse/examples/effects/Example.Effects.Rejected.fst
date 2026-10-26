module Example.Effects.Rejected
#lang-pulse

(* Negative specification tests for the effect and exception interfaces.

   Each declaration is intentionally invalid, and expect_failure requires F*
   to reject it with the indicated error category. Thus successful verification
   of this module means the misuse was rejected, not accepted or admitted.
   These cases exercise stale ownership, execution without ownership, unhandled
   effects, stranded abort frames, and incorrect exceptional-state reasoning.

   This module is checked by the default build but is not part of the extracted
   runtime entry point. The positive examples supply the contracts being misused;
   these tests should fail at those contracts, not at missing names or imports. *)

open Pulse.Lib.Pervasives
// E/X/R are the core, exception, and reference APIs under test.
// C and Ex reuse the positive examples' exact operation and exception protocols.
module E = Pulse.Lib.Effects.Core
module X = Pulse.Lib.Effects.Exception
module R = Pulse.Lib.Reference
module C = Example.Effects.Core
module Ex = Example.Effects.Exception

// Exchange transfers r from state 0 to state 1. The next computation wrongly
// tries to read it under r |-> 0. Error 19 must reject the continuation's resource
// index: receiving the old integer does not restore the old heap assertion.
[@@expect_failure [19]]
let stale_ownership (r:ref int)
  : E.prog (C.ops r) int (R.pts_to r 0)
      (fun n -> R.pts_to r 0 ** pure (n == 0)) =
  E.bind (E.perform #C.op #(C.ops r) C.Exchange (hide 0, 1))
    (fun _ -> E.lift (fun () -> C.read_initial r))

// A tree value is not permission to execute it. This function starts with no
// owned cell, yet client requires r |-> 0. Pulse must fail to supply that request
// ownership (error 228), despite the desired final state being well specified.
[@@expect_failure [228]]
fn missing_request_ownership (r:ref int)
  returns n:int
  ensures R.pts_to r 2 ** pure (n == 42)
{
  E.run #C.op #(C.ops r) (C.exchange r) (C.client r)
}

// Pretend that a body with an outstanding exception has the empty base signature.
// Error 12 rejects this type mismatch before a caller can pass it to run_closed;
// returning an int does not by itself mean all effects have been handled.
[@@expect_failure [12]]
let unhandled_exception (r:ref int)
  : E.prog Ex.empty_ops int (R.pts_to r 0) (Ex.normal r true) =
  Ex.body r true

// Construct a raw Throw with a second cell in its private frame, then try to
// claim it belongs to X.prog. Error 19 must reject the transfers_frame refinement.
// The second cell is not in exceptional, and the impossible continuation cannot
// be relied on to consume it. This guards against silently leaking abort ownership.
[@@expect_failure [19]]
let stranded_frame (r other:ref int)
  : X.prog Ex.empty_ops (Ex.exceptional r true) int
      (Ex.exceptional r true Ex.Boom ** R.pts_to other 7)
      (fun _ -> emp) =
  E.Perform #_ #(X.extend Ex.empty_ops (Ex.exceptional r true))
    #int #_ #(R.pts_to other 7) X.Throw Ex.Boom
    (fun impossible -> match impossible with)

// The exceptional protocol promises r |-> 1 before recovery. Claiming that a
// read yields 0 must fail (error 19), even though the function otherwise preserves
// the cell. This checks the exception-entry state, not the handler's final state.
[@@expect_failure [19]]
fn wrong_exception_state (r:ref int)
  requires Ex.exceptional r true Ex.Boom
  ensures R.pts_to r 1
{
  unfold (Ex.exceptional r true Ex.Boom);
  let n = !r;
  assert pure (n == 0);
}
