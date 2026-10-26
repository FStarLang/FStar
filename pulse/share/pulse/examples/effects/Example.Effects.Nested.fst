module Example.Effects.Nested
#lang-pulse

(* Two nested exception layers with policy-preserving forwarding.

   Both layers carry unit payloads, so routing depends on tags, not payload
   types: Throw addresses the inner layer and Other Throw addresses the outer.
   The original body never returns normally. Catching an inner throw produces
   int 10 with r at 2; the outer normal clause then returns true. An outer throw
   passes through the inner handler and is caught at the outer layer, which
   writes 3 and returns false.

   The critical proof exercise is retaining the outer layer's empty-frame
   discipline while removing the inner layer. Explicit all_requests proofs
   and catch_all_requests make the inner handler's output acceptable to the
   outer catch. The final result/state is (true, 2) or (false, 3). *)

open Pulse.Lib.Pervasives
// E supplies generic policy lemmas; X builds and removes exception layers;
// R supplies the shared cell whose ownership must follow the selected route.
module E = Pulse.Lib.Effects.Core
module X = Pulse.Lib.Effects.Exception
module R = Pulse.Lib.Reference

// Base environment after both exception layers have been removed.
let empty_ops : E.signature E.empty = fun impossible -> match impossible with

// Entry ownership for the inner exception, including evidence of its selection.
let inner_pre (r:ref int) (choose_inner:bool) (_:unit) =
  R.pts_to r 0 ** pure choose_inner

// Entry ownership for the outer exception. Forwarding must preserve r at 0
// until the outer clause runs; the inner recovery clause must not have run.
let outer_pre (r:ref int) (choose_inner:bool) (_:unit) =
  R.pts_to r 0 ** pure (not choose_inner)

// The outer exception layer, with no effects left beneath it.
let outer_ops r b = X.extend empty_ops (outer_pre r b)

// The inner layer wrapped around outer_ops. Its Other constructor shifts the
// interpretation of an outer Throw without changing that operation's contract.
let both_ops r b = X.extend (outer_ops r b) (inner_pre r b)

// The property the intermediate tree must satisfy to enter the outer catch.
let outer_policy r b = X.frame_policy empty_ops (outer_pre r b)

// View the outer property in the two-layer environment. Local inner throws are
// ignored by this property, while Other Throw must still retain an empty frame.
let forwarded r b =
  X.forwarded_policy (outer_ops r b) (inner_pre r b) (outer_policy r b)

// Package unchanged cell ownership and the branch fact as an inner request.
// This logical preparation is a Pulse step, illustrating policies through Step.
fn prepare_inner (r:ref int) (b:bool{b})
  requires R.pts_to r 0
  ensures inner_pre r b ()
{
  fold (inner_pre r b ());
}

// Package unchanged ownership for an outer request without updating the cell.
// The enclosing inner handler will have to forward this protocol intact.
fn prepare_outer (r:ref int) (b:bool{not b})
  requires R.pts_to r 0
  ensures outer_pre r b ()
{
  fold (outer_pre r b ());
}

// Request the local Throw using Core.perform, whose reply type here is empty.
// Establish both the local exception refinement and the forwarded outer policy.
// assert_norm aligns the protocol's reply function with the explicit emp
// postcondition used in the result type; it adds no assumption about execution.
let request_inner (r:ref int) (b:bool)
  : c:X.prog (outer_ops r b) (inner_pre r b)
      E.empty (inner_pre r b ()) (fun _ -> emp)
      {E.all_requests c (forwarded r b)} =
  assert_norm ((both_ops r b X.Throw).E.reply () == (fun (_:E.empty) -> emp));
  E.perform_all_requests #_ #(both_ops r b) X.Throw ()
    (X.frame_policy (outer_ops r b) (inner_pre r b));
  E.perform_all_requests #_ #(both_ops r b) X.Throw () (forwarded r b);
  E.perform #_ #(both_ops r b) X.Throw ()

// Request Other Throw. The inner policy allows this tag, but the forwarded
// outer policy still checks its frame is emp. These two proofs prevent an inner
// catch from hiding an outer throw that strands ownership.
let request_outer (r:ref int) (b:bool)
  : c:X.prog (outer_ops r b) (inner_pre r b)
      E.empty (outer_pre r b ()) (fun _ -> emp)
      {E.all_requests c (forwarded r b)} =
  assert_norm ((both_ops r b (X.Other X.Throw)).E.reply () == (fun (_:E.empty) -> emp));
  E.perform_all_requests #_ #(both_ops r b) (X.Other X.Throw) ()
    (X.frame_policy (outer_ops r b) (inner_pre r b));
  E.perform_all_requests #_ #(both_ops r b) (X.Other X.Throw) () (forwarded r b);
  E.perform #_ #(both_ops r b) (X.Other X.Throw) ()

// Prepend a resource-preparing action to a request satisfying both policies.
// Use step_all_requests twice rather than relying on incidental SMT unfolding
// of a continuation function. s is the intermediate request ownership.
let prefix (r:ref int) (b:bool) (#s:slprop)
  (action:unit -> stt unit (R.pts_to r 0) (fun _ -> s))
  (request:(c:X.prog (outer_ops r b) (inner_pre r b) E.empty s (fun _ -> emp)
    {E.all_requests c (forwarded r b)}))
  : c:X.prog (outer_ops r b) (inner_pre r b)
      E.empty (R.pts_to r 0) (fun _ -> emp)
      {E.all_requests c (forwarded r b)} =
  let local = X.frame_policy (outer_ops r b) (inner_pre r b) in
  let next (_:unit) = request in
  E.step_all_requests action next local;
  E.step_all_requests action next (forwarded r b);
  E.Step action next

// Select an inner or outer throw, preserving both policy proofs in either case.
// The normal result type is empty: both routes must be handled, and neither
// normal continuation can be invoked before an exception clause intervenes.
let body (r:ref int) (b:bool)
  : c:X.prog (outer_ops r b) (inner_pre r b)
      E.empty (R.pts_to r 0) (fun _ -> emp)
      {E.all_requests c (forwarded r b)} =
  if b then
    prefix r b (fun () -> prepare_inner r b) (request_inner r b)
  else
    prefix r b (fun () -> prepare_outer r b) (request_outer r b)

// A normal result after the inner catch witnesses that the inner route won.
// The outer-exception route cannot return this state/result normally.
let inner_done (r:ref int) (b:bool) (n:int) =
  R.pts_to r 2 ** pure (b /\ n == 10)

// Recover the inner request's ownership, write 2, and produce the intermediate
// integer 10. The outer layer will subsequently handle this normal completion.
fn inner_clause (r:ref int) (b:bool) (_:unit)
  requires inner_pre r b ()
  returns n:int
  ensures inner_done r b n
{
  unfold (inner_pre r b ());
  r := 2;
  fold (inner_done r b 10);
  10
}

// Remove only the inner exception and change the normal result type from empty
// to int. catch_all_requests establishes that the output retains the outer
// frame policy, so its type is X.prog rather than merely an unrestricted E.prog.
let handle_inner (r:ref int) (b:bool)
  : X.prog empty_ops (outer_pre r b) int (R.pts_to r 0) (inner_done r b) =
  let c = body r b in
  // The original body cannot complete normally; no normal resources are lost.
  let on_return (impossible:E.empty)
    : X.prog empty_ops (outer_pre r b) int emp (inner_done r b) =
    match impossible with
  in
  // A lifted recovery action has no outer requests, hence meets outer_policy.
  let on_throw (e:unit)
    : X.prog empty_ops (outer_pre r b) int (inner_pre r b e) (inner_done r b) =
    X.lift (fun () -> inner_clause r b e)
  in
  X.catch_all_requests c on_return on_throw (outer_policy r b);
  X.catch c on_return on_throw

// Final observable behavior, indexed by the chosen exception layer.
// It connects the bool returned by the outer handler to the concrete cell state.
let done_ (r:ref int) (b:bool) (result:bool) =
  R.pts_to r (if b then 2 else 3) ** pure (result == b)

// Translate the inner handler's successful integer result into bool true,
// retaining r at 2. This exercises a handler that changes the result type.
fn outer_return (r:ref int) (b:bool) (n:int)
  requires inner_done r b n
  returns result:bool
  ensures done_ r b result
{
  unfold (inner_done r b n);
  fold (done_ r b true);
  true
}

// Catch the forwarded outer throw, which still owns r at 0. Write 3 and return
// false; the precondition excludes a preceding run of the inner recovery clause.
fn outer_clause (r:ref int) (b:bool) (_:unit)
  requires outer_pre r b ()
  returns result:bool
  ensures done_ r b result
{
  unfold (outer_pre r b ());
  r := 3;
  fold (done_ r b false);
  false
}

// Remove the final exception layer, changing int to bool and producing an
// empty-environment computation suitable for the ordinary closed interpreter.
let handle_outer (r:ref int) (b:bool)
  : E.prog empty_ops bool (R.pts_to r 0) (done_ r b) =
  X.catch (handle_inner r b)
    (fun n -> E.lift (fun () -> outer_return r b n))
    (fun e -> E.lift (fun () -> outer_clause r b e))

// Observe the complete nested-handler behavior with a fresh cell. The proof is
// uniform in choose_inner; the executable suite specializes its two tree shapes
// and compares both the routing result and the final state.
fn test ([@@@FStar.Attributes.monomorphize] choose_inner:bool)
  returns result:bool & int
  ensures pure (result == (choose_inner, (if choose_inner then 2 else 3)))
{
  let mut r = 0;
  let result = E.run_closed (handle_outer r choose_inner);
  unfold (done_ r choose_inner result);
  let value = !r;
  (result, value)
}
