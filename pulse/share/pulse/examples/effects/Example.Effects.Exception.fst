module Example.Effects.Exception
#lang-pulse

(* A complete verified raise/catch scenario with concrete ownership recovery.

   Starting with r |-> 0, the throwing branch writes 1 and transfers that
   ownership in Boom's exceptional contract. Its handler writes 2 and returns
   42. The normal branch writes 3 and returns 7, without running the exception
   clause. Thus test returns (42, 2) or (7, 3), not merely an unconstrained int.

   A syntactically sequenced write of 99 after throw has an impossible
   precondition and must never run. framed_test separately exercises framing
   around the already handled computation, not around an open throwing tree.
   The proofs quantify over the branch flag; runtime extraction specializes
   that flag to true and false in Example.Effects.Runtime. *)

open Pulse.Lib.Pervasives
// E executes closed descriptions; X provides disciplined abortive operations;
// R tracks the concrete cell whose ownership crosses the exception boundary.
module E = Pulse.Lib.Effects.Core
module X = Pulse.Lib.Effects.Exception
module R = Pulse.Lib.Reference

// One payload constructor is enough to isolate control and ownership behavior;
// the protocol below also carries the branch fact and reference state.
type exception_value = | Boom

// There are no effects other than the exception layer introduced by X.prog.
// After catch removes that layer, this signature permits E.run_closed.
let empty_ops : E.signature E.empty = fun impossible -> match impossible with

// Ownership delivered to the exception clause, before recovery runs: r is at 1.
// The pure flag rules out this path in the normal-completion scenario.
let exceptional (r:ref int) (raise_it:bool) (_:exception_value) =
  R.pts_to r 1 ** pure raise_it

// Contract for a normal return of the unhandled body. A throwing body can have
// this contract even though it cannot establish it by returning: it never does.
let normal (r:ref int) (raise_it:bool) (n:int) =
  R.pts_to r 3 ** pure (not raise_it /\ n == 7)

// Common postcondition of both handler clauses. It records which control path
// occurred through exact, flag-indexed state and result values.
let handled (r:ref int) (raise_it:bool) (n:int) =
  R.pts_to r (if raise_it then 2 else 3) **
  pure (n == (if raise_it then 42 else 7))

// Establish the entire exceptional ownership before requesting Boom. No private
// frame is needed at the throw because the protocol already carries the cell.
fn prepare_throw (r:ref int) (raise_it:bool{raise_it})
  requires R.pts_to r 0
  ensures exceptional r raise_it Boom
{
  r := 1;
  fold (exceptional r raise_it Boom);
}

// Deliberately unreachable continuation code. Its pure False precondition makes
// its normal specification provable, but supplies no way to call it in a real
// execution. The write of 99 is a recognizable marker, not a recovery action.
fn dead_write (r:ref int) (raise_it:bool)
  requires R.pts_to r 1 ** pure False
  returns n:int
  ensures normal r raise_it n
{
  r := 99;
  fold (normal r raise_it 7);
  7
}

// The non-throwing alternative: update directly from 0 to 3 and return 7.
// Its refined flag justifies the normal contract consumed by return_clause.
fn complete_normally (r:ref int) (raise_it:bool{not raise_it})
  requires R.pts_to r 0
  returns n:int
  ensures normal r raise_it n
{
  r := 3;
  fold (normal r raise_it 7);
  7
}

// Build, but do not execute, the selected branch. In the throwing branch,
// X.throw is instantiated with an impossible normal postcondition so subsequent
// code can be typed without claiming that it is reachable. X.bind must bypass
// dead_write when the local exception is caught.
let body (r:ref int) (raise_it:bool)
  : X.prog empty_ops (exceptional r raise_it)
      int (R.pts_to r 0) (normal r raise_it) =
  if raise_it then
    X.bind (X.lift (fun () -> prepare_throw r raise_it)) (fun _ ->
      X.bind
        (X.throw #E.empty #exception_value #unit #empty_ops
          #(exceptional r raise_it) #(fun _ -> R.pts_to r 1 ** pure False) Boom)
        (fun _ -> X.lift (fun () -> dead_write r raise_it)))
  else X.lift (fun () -> complete_normally r raise_it)

// Adapt normal completion to the common handled postcondition without another
// heap update or a replacement result. This clause must see the normal flag.
fn return_clause (r:ref int) (raise_it:bool) (n:int)
  requires normal r raise_it n
  returns result:int
  ensures handled r raise_it result
{
  unfold (normal r raise_it n);
  fold (handled r raise_it n);
  n
}

// Recover ownership from exceptional r raise_it e, use it to write 2, and
// replace the abandoned body's result with 42. There is no continuation to call.
fn exception_clause (r:ref int) (raise_it:bool) (e:exception_value)
  requires exceptional r raise_it e
  returns result:int
  ensures handled r raise_it result
{
  unfold (exceptional r raise_it e);
  r := 2;
  fold (handled r raise_it 42);
  42
}

// Assemble this example's handler using the library's X.catch. Despite its
// local name, this is not a use of the library's frame-polymorphic X.handle.
// Both clauses are lifted Pulse computations and the output environment is empty.
let handle (r:ref int) (raise_it:bool)
  : E.prog empty_ops int (R.pts_to r 0) (handled r raise_it) =
  X.catch (body r raise_it)
    (fun n -> E.lift (fun () -> return_clause r raise_it n))
    (fun e -> E.lift (fun () -> exception_clause r raise_it e))

// Execute a freshly allocated closed computation and observe both result and
// final heap state. Both cases are proved uniformly; monomorphize specializes
// their tree shapes for the two calls made by the extracted runtime suite.
fn test ([@@@FStar.Attributes.monomorphize] raise_it:bool)
  returns result:int & int
  ensures pure (result == (if raise_it then (42, 2) else (7, 3)))
{
  let mut r = 0;
  let result = E.run_closed (handle r raise_it);
  unfold (handled r raise_it result);
  let value = !r;
  (result, value)
}

// Exercise Pulse's ordinary frame rule around execution after catch has removed
// the exception. The unrelated cell remains at 17 without being included in
// Boom's protocol. This helper is verified, but not called by Runtime.test.
fn framed_test (r other:ref int)
  requires R.pts_to r 0 ** R.pts_to other 17
  returns result:int
  ensures R.pts_to r 2 ** R.pts_to other 17 ** pure (result == 42)
{
  let result = E.run_closed (handle r true);
  unfold (handled r true result);
  result
}
