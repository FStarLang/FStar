module Example.Effects.Core
#lang-pulse

(* Returning operations, delayed Pulse steps, framing, and effect forwarding.

   The client reads a reference at 0, requests an exchange to 1, then writes 2
   and returns 42. The operation returns both the old integer and the ownership
   needed to prove it was 0. This exercises an operation protocol that changes
   the heap assertion rather than merely carrying a pure result.

   test additionally constructs the tree before reading the initial state,
   forwards its requests through an exception layer that cannot throw, and
   frames a second reference. Its observed tuple is (0, 42, 2, 7).
   positive_client separately checks consequence/postcondition weakening; it is
   verified here but is not a separate case in the extracted runtime suite.
   See README.md for the suite map and how to run it. *)

open Pulse.Lib.Pervasives
// E supplies trees/interpreters; X supplies a removable exception layer;
// R supplies the concrete reference ownership used in every operation contract.
module E = Pulse.Lib.Effects.Core
module X = Pulse.Lib.Effects.Exception
module R = Pulse.Lib.Reference

// Two distinguishable tags intentionally share one protocol. The client selects
// Exchange or ExchangeAgain from a value obtained by a delayed Pulse read.
type op = | Exchange | ExchangeAgain

// Parameterize the whole signature by the reference being managed. Each input
// pairs an erased old-state witness with a runtime new value. request transfers
// ownership at that old state; reply transfers ownership at the new state and
// proves the returned integer equals the witness.
let ops (r:ref int) : E.signature op = fun _ -> {
  E.input = erased int & int;
  E.output = int;
  E.request = (fun arg -> R.pts_to r (reveal (fst arg)));
  E.reply = (fun arg old ->
    R.pts_to r (snd arg) ** pure (old == reveal (fst arg)));
}

// Implement either exchange tag: read the old value and install the new one.
// The old-state witness is proof-only, whereas both the update and returned
// integer are real runtime behavior checked by the executable scenario.
fn exchange (r:ref int) (_:op) (arg:erased int & int)
  requires R.pts_to r (reveal (fst arg))
  returns old:int
  ensures R.pts_to r (snd arg) ** pure (old == reveal (fst arg))
{
  let old = !r;
  r := snd arg;
  old
}

// A heap-reading Pulse step whose result becomes input to later tree construction.
// Preserve r |-> 0 and expose the pure fact that its read result is 0.
fn read_initial (r:ref int)
  requires R.pts_to r 0
  returns n:int
  ensures R.pts_to r 0 ** pure (n == 0)
{
  !r
}

// Consume the exchange reply: r must now contain 1, and old must be 0.
// Write the final state 2 and calculate 42 from the actual reply value.
fn finish (r:ref int) (old:int)
  requires R.pts_to r 1 ** pure (old == 0)
  returns n:int
  ensures R.pts_to r 2 ** pure (n == 42)
{
  r := 2;
  old + 42
}

// Discharge the initial read's pure assertion while retaining all heap ownership.
// This aligns the next Step's postcondition with the exchange request precondition;
// it is logical weakening, not disposal of the reference.
fn forget_initial (r:ref int) (n:int)
  requires R.pts_to r 0 ** pure (n == 0)
  ensures R.pts_to r 0
{
}

// Compose read -> request -> finish using lift, an explicit Step, and bind.
// The request tag depends on the read result; the erased witness hide 0 records
// the state transferred to the operation. The final contract pins both r = 2
// and result = 42, so a missing update or wrong reply cannot satisfy it.
let client (r:ref int)
  : E.prog (ops r) int (R.pts_to r 0)
      (fun n -> R.pts_to r 2 ** pure (n == 42)) =
  E.bind (E.lift (fun () -> read_initial r)) (fun n ->
    E.Step
      (fun () -> forget_initial r n)
      (fun _ ->
        E.bind
          (E.perform #(op) #(ops r)
            (if n = 0 then Exchange else ExchangeAgain) (hide 0, 1))
          (fun old -> E.lift (fun () -> finish r old))))

// Exercise the explicit tree-level frame combinator around the state client.
// The operation implementation receives only r; ownership of other at 7 must
// survive each Step and Perform in the constructed description.
fn framed (r other:ref int)
  requires R.pts_to r 0 ** R.pts_to other 7
  returns n:int
  ensures (R.pts_to r 2 ** pure (n == 42)) ** R.pts_to other 7
{
  let c = E.frame (R.pts_to other 7) (client r);
  E.run #op #(ops r) (exchange r) c
}

// The exception payload type is empty, so no value can initiate a local throw.
// This lets the next scenario isolate forwarding from exception recovery.
let no_exception (impossible:E.empty) : slprop = match impossible with

// Embed the client as Other requests and then remove the empty exception layer.
// The normal clause returns its input; the exceptional clause is impossible.
// Both exchange tags must reach the original operation implementation unchanged.
let through_handler (r:ref int)
  : E.prog (ops r) int (R.pts_to r 0)
      (fun n -> R.pts_to r 2 ** pure (n == 42)) =
  X.catch
    (X.weaken #op #E.empty #int #(ops r) #no_exception (client r))
    (fun n -> E.Return n)
    (fun impossible -> match impossible with)

// Identity precondition entailment for consequence. Even an unchanged entry
// assertion is supplied as a checked ghost computation, not assumed.
ghost fn preserve_initial (r:ref int) ()
  requires R.pts_to r 0
  ensures R.pts_to r 0
{
}

// Weaken the precise result fact n = 42 to n > 0, retaining ownership at state 2.
// This demonstrates a usable consequence rule over both pure and spatial facts.
ghost fn positive_result (r:ref int) (n:int)
  requires R.pts_to r 2 ** pure (n == 42)
  ensures R.pts_to r 2 ** pure (n > 0)
{
}

// Present the same client under a less precise result contract using the two
// ghost entailments above. This is a verification-only API-composition example;
// the runtime entry below keeps the stronger exact-result contract instead.
let positive_client (r:ref int)
  : E.prog (ops r) int (R.pts_to r 0)
      (fun n -> R.pts_to r 2 ** pure (n > 0)) =
  E.consequence (preserve_initial r) (client r) (positive_result r)

// Runtime observation of delayed construction, forwarding, and explicit framing.
// Return (state before execution, result, final state, framed reference value).
// The read after constructing c must still see 0: construction is not execution.
fn test ()
  returns result:int & int & int & int
  ensures pure (result == (0, 42, 2, 7))
{
  let mut r = 0;
  let mut other = 7;
  let c = E.frame (R.pts_to other 7) (through_handler r);
  let before = !r;
  assert pure (before == 0);
  let result = E.run #op #(ops r) (exchange r) c;
  let after = !r;
  assert pure (after == 2);
  let untouched = !other;
  assert pure (untouched == 7);
  (before, result, after, untouched)
}
