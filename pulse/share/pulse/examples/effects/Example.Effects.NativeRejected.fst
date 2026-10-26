module Example.Effects.NativeRejected
#lang-pulse

(* Rejection tests for native exception checking. Each case is syntactically
   valid and must fail at its effect or resource obligation, not at extraction. *)

open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module B = Pulse.Lib.Box
module N = Example.Effects.Native
module E = Pulse.Lib.Effects.Rules

// Ignoring a call's result is not an exception handler. The checker must split
// native calls even when the enclosing function has no raises annotation.
[@@expect_failure [19]]
fn ignored_exception ()
{
  let _ = N.maybe_value true;
  ()
}

// Calls cannot bypass the cleanup boundary by discarding their result either.
[@@expect_failure [19]]
fn cleanup_call_escapes ()
  raises (fun (_:nat) -> emp)
{
  defer emp { let _ = N.maybe_value true; () };
  raise 1
}

// A local function cannot capture the defining function's exception exit.
// It must declare its own raises contract, which its caller then propagates.
[@@expect_failure [19]]
fn captured_exception_exit ()
  raises (fun (_:nat) -> emp)
{
  fn local () { raise 1 };
  local ()
}

// Catching a call's exceptions does not prove it terminates before raising.
// A surrounding defer must preserve this divergent effect too.
[@@expect_failure [228]]
fn catch_is_not_termination ()
  returns x:int
  ensures pure (x == 7)
{
  defer emp { () };
  try
    returns x:int
    ensures pure (x == 7)
    raises (fun (e:nat) -> pure (e == 1))
  { N.raise_code 1 }
  catch { 1 -> { 7 } }
}

// A return escaping cleanup can abandon the pending exception's resources just
// as an escaping raise can. The normal-only cleanup rule permits neither.
[@@expect_failure [228]]
fn cleanup_return_abandons_exception (r:ref int)
  requires R.pts_to r 0
  raises (fun (_:nat) -> R.pts_to r 1)
{
  defer emp { return () };
  r := 1;
  raise 1
}

// Raising does not manufacture the ownership promised to a handler.
[@@expect_failure [228]]
fn missing_exception_resource (r:ref int)
  returns x:int
  ensures pure False
  raises (fun (_:nat) -> R.pts_to r 1)
{
  raise 1
}

// The frame of a throwing call must be included in its exceptional exit.
[@@expect_failure [228]]
divergent fn lost_frame (r other:ref int)
  requires R.pts_to r 0 ** R.pts_to other 17
  returns x:int
  ensures pure False
  raises (N.failed r)
{
  N.update_and_raise r false
}

// emp allows an exception with no resources; it does not forbid exceptions.
// This handler covers First, but Second remains possible.
[@@expect_failure [19]]
fn unmatched ()
{
  try
    raises (fun (_:N.failure) -> emp)
  { raise N.Second }
  catch { N.First -> { () } }
}

// The same handler does not catch an exception re-raised by its own clause.
[@@expect_failure [19]]
fn unhandled_reraise ()
{
  try
    raises (fun (e:nat) -> pure (e == 1))
  { raise 1 }
  catch { 1 -> { raise 1 } }
}

// A catch clause owns the throwing state, not the pre-call state.
[@@expect_failure [19]]
divergent fn stale_handler_state (r:ref int)
  requires R.pts_to r 0
  returns x:int
  ensures R.pts_to r 3
{
  try
    returns x:int
    ensures R.pts_to r 3
    raises (N.failed r)
  { N.update_and_raise r false }
  catch {
    e -> {
      let value = !r;
      assert pure (value == 0);
      r := 3;
      0
    }
  }
}

// Raising is forbidden in ghost and atomic computations, even with an empty
// resource context.
[@@expect_failure [228]]
ghost fn ghost_raise ()
{ raise 1 }

[@@expect_failure [228]]
atomic fn atomic_raise ()
{ raise 1 }

// The normal-only defer rule cannot justify abandoning a pending exception's
// resources when cleanup throws a replacement exception.
[@@expect_failure [19]]
fn escaping_cleanup ()
  raises (fun (_:nat) -> emp)
{
  defer emp { raise 2 };
  raise 1
}

// Scope reclamation still requires full ownership of the local. Handing half
// of its permission to the handler cannot leave enough to reclaim the cell.
[@@expect_failure [19]]
fn escaped_local_permission ()
  raises (fun (r:ref int) -> R.pts_to r #0.5R 0)
{
  let mut local = 0;
  R.share local;
  raise local
}

// An ordinary return inside a try also aborts the protected continuation. It
// must not hide an unreturned frame behind that continuation's impossible post.
[@@expect_failure [228]]
fn return_abandons_frame ()
  raises (fun (_:nat) -> emp)
{
  let box = B.alloc 0;
  try
    ensures pure False
    raises (fun (_:nat) -> B.pts_to box 0)
  { return () }
  catch { _ -> { B.free box; raise 1 } }
}

// Catching and re-raising changes control, not the ownership conservation rule.
[@@expect_failure [228]]
divergent fn reraise_abandons_resource (r:ref int)
  requires R.pts_to r 0
  returns x:int
  ensures pure False
  raises (fun (_:N.failure) -> emp)
{
  try
    returns x:int
    ensures pure False
    raises (N.failed r)
  { N.update_and_raise r false }
  catch { e -> { raise e } }
}
