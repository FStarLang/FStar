module Example.Effects.Native
#lang-pulse

(* Native exception scenarios. These use raises/raise/try/catch directly,
   without constructing effect trees. Custard extraction is a separate stage. *)

open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module E = Pulse.Lib.Effects.Rules
module B = Pulse.Lib.Box

// An abortive function has an impossible normal postcondition and transfers
// the exact payload fact on its exceptional exit.
divergent fn raise_code (code:nat)
  returns x:int
  ensures pure False
  raises (fun (e:nat) -> pure (e == code))
{
  raise code
}

// The call is automatically split into normal and exceptional continuations.
// Only payload 1 is possible, so the implicit unmatched branch is unreachable.
divergent fn catch_code ()
  returns x:int
  ensures pure (x == 7)
{
  try
    returns x:int
    ensures pure (x == 7)
    raises (fun (e:nat) -> pure (e == 1))
  {
    raise_code 1
  }
  catch {
    1 -> { 7 }
  }
}

// Each exception constructor carries ownership of the updated cell. The
// exceptional contract is a resource protocol, not just a set of names.
type failure = | First | Second

[@@pulse_unfold]
let failed (r:ref int) (e:failure) =
  R.pts_to r (match e with First -> 1 | Second -> 2)

// A local scope is crossed by the exceptional exit. Its temporary is reclaimed
// automatically, while the caller-owned cell is transferred through failed.
divergent fn update_and_raise (r:ref int) (second:bool)
  requires R.pts_to r 0
  returns x:int
  ensures pure False
  raises (failed r)
{
  let mut temporary = 10;
  temporary := 11;
  if (second) {
    r := 2;
    raise Second
  } else {
    r := 1;
    raise First
  }
}

// Only First is handled. Second is forwarded, and the outer raises contract
// excludes First using a payload fact. No satisfiability test on slprops occurs.
divergent
fn partial (r:ref int) (second:bool)
  requires R.pts_to r 0
  returns x:int
  ensures R.pts_to r 3 ** pure (x == 30)
  raises (fun (e:failure) -> failed r e ** pure (e == Second))
{
  try
    returns x:int
    ensures R.pts_to r 3 ** pure (x == 30)
    raises (failed r)
  {
    update_and_raise r second
  }
  catch {
    First -> { r := 3; 30 }
  }
}

// A caught First is re-raised after changing its owned state. The inner catch
// must not intercept its own clause's exception. The outer handler receives 4,
// not the original throwing state 1, and the inner local has already gone away.
fn reraised (r:ref int)
  requires R.pts_to r 0
  returns x:int
  ensures R.pts_to r 5 ** pure (x == 50)
{
  try
    returns x:int
    ensures R.pts_to r 5 ** pure (x == 50)
    raises (fun (e:failure) -> R.pts_to r 4 ** pure (e == First))
  {
    try
      returns x:int
      ensures R.pts_to r 5 ** pure (x == 50)
      raises (fun (e:failure) -> R.pts_to r 1 ** pure (e == First))
    {
      let mut temporary = 10;
      r := 1;
      raise First
    }
    catch {
      First -> { r := 4; raise First }
    }
  }
  catch {
    First -> { r := 5; 50 }
  }
}

// A handler inside the local's scope retains access to it. Only the eventual
// function exit reclaims that cell.
fn handler_inside_scope ()
  returns x:int
  ensures pure (x == 12)
{
  let mut local = 0;
  try
    returns x:int
    ensures R.pts_to local 12 ** pure (x == 12)
    raises (fun (e:nat) -> R.pts_to local 11 ** pure (e == 1))
  {
    local := 11;
    raise 1
  }
  catch {
    1 -> { local := 12; !local }
  }
}

// Both exits of a call are framed with other |-> 17. Second still propagates,
// so preserving that unrelated cell cannot rely on a handler running.
divergent fn framed_call (r other:ref int) (second:bool)
  requires R.pts_to r 0 ** R.pts_to other 17
  returns x:int
  ensures R.pts_to r 3 ** R.pts_to other 17 ** pure (x == 30)
  raises (fun (e:failure) ->
    failed r e ** R.pts_to other 17 ** pure (e == Second))
{
  partial r second
}

// Normal completion and throwing are independent of divergence. The payload
// and return facts identify exactly which branch ran.
fn maybe_value (b:bool)
  returns x:int
  ensures pure (not b /\ x == 7)
  raises (fun (e:nat) -> pure (b /\ e == 1))
{
  if (b) { raise 1 } else { 7 }
}

// A try expression can initialize a local binding; its ordinary continuation
// runs after either normal completion or recovery.
fn catch_then_continue (b:bool)
  returns x:int
  ensures pure (x == (if b then 43 else 8))
{
  let result = try
    returns x:int
    ensures pure (x == (if b then 42 else 7))
    raises (fun (e:nat) -> pure (b /\ e == 1))
  {
    maybe_value b
  }
  catch {
    1 -> { 42 }
  };
  result + 1
}

// Higher-order native computation types carry the same two exits as declared
// functions. Calling action must propagate its exception, not return an outcome
// value to the user-written continuation.
fn invoke
  (action:fn (b:bool)
    returns x:int
    ensures pure (not b /\ x == 7)
    raises (fun (e:nat) -> pure (b /\ e == 1)))
  (b:bool)
  returns x:int
  ensures pure (not b /\ x == 7)
  raises (fun (e:nat) -> pure (b /\ e == 1))
{
  action b
}

// Nonraising cleanup runs on exceptional exit and consumes real heap ownership.
// The box is not a scoped local and would leak without the defer.
divergent fn deferred_free ()
  returns x:int
  ensures pure False
  raises (fun (e:nat) -> pure (e == 1))
{
  let box = B.alloc 0;
  defer (B.pts_to box 0) { B.free box };
  raise 1
}

// Cleanup may raise and handle exceptions internally; only an escaping raise is
// prohibited. This is not a restriction on re-raising in ordinary catch clauses.
divergent fn cleanup_handles_locally ()
  returns x:int
  ensures pure False
  raises (fun (e:nat) -> pure (e == 1))
{
  let box = B.alloc 0;
  defer (B.pts_to box 0) {
    try
      ensures B.pts_to box 0
      raises (fun (e:nat) -> B.pts_to box 0 ** pure (e == 2))
    { raise 2 }
    catch { 2 -> { () } };
    B.free box
  };
  raise 1
}

// A break targeting a loop inside cleanup is local control flow, not an escape
// from cleanup. It leaves the pending exception and its ownership unchanged.
divergent fn cleanup_local_loop ()
  raises (fun (e:nat) -> pure (e == 1))
{
  defer emp {
    while (true)
      invariant emp
      ensures True
    { break };
  };
  raise 1
}

// Exceptional control crosses a loop without having to establish another
// iteration's invariant. Ownership of r moves to the enclosing raises contract.
divergent fn loop_exit (r:ref int)
  requires R.pts_to r 0
  ensures R.pts_to r 0 ** pure False
  raises (fun (e:nat) -> R.pts_to r 1 ** pure (e == 1))
{
  while (true)
    invariant R.pts_to r 0
  {
    r := 1;
    raise 1
  }
}

// The ordinary continuation receives an int, not the internal outcome. It is
// skipped on the exceptional path, preserving the callee's payload facts.
fn increment_result (b:bool)
  returns x:int
  ensures pure (not b /\ x == 8)
  raises (fun (e:nat) -> pure (b /\ e == 1))
{
  let x = maybe_value b;
  x + 1
}

// A native call needs no handler when its instantiated exceptional post is
// impossible. The result still reaches the ordinary continuation as an int.
fn known_normal ()
  returns x:int
  ensures pure (x == 8)
{
  let x = maybe_value false;
  x + 1
}

// Raw semantic outcomes are data, even inside a native exception scope. This
// distinction lets the derived proof rules remain usable as ordinary libraries.
// The literal stt type exposes the computation to Pulse's existing readback.
let raw_raise (code:nat)
  : stt (E.outcome nat int) emp
      (fun v -> E.exit_post (fun _ -> emp) (fun _ -> emp) v)
  = E.raise_ code

fn raw_outcome ()
  returns x:int
  ensures pure (x == 9)
  raises (fun (_:nat) -> pure False)
{
  let v = raw_raise 1;
  match v {
    E.Normal _ -> { 9 }
    E.Raised _ -> { 9 }
  }
}

// A handler may replace the caught exception as well as update its resources.
// This catch translates either failure constructor to Second.
divergent fn translate (r:ref int)
  requires R.pts_to r 0
  returns x:int
  ensures pure False
  raises (fun (e:failure) -> R.pts_to r 4 ** pure (e == Second))
{
  try
    returns x:int
    ensures pure False
    raises (failed r)
  { update_and_raise r false }
  catch { _ -> { r := 4; raise Second } }
}

// Recursive calls use the declared exceptional contract just like other calls.
divergent fn rec countdown (n:nat)
  returns x:int
  ensures pure False
  raises (fun (e:nat) -> pure (e == 0))
{
  if (n = 0) { raise 0 }
  else { countdown (n - 1) }
}

// The write after raise is unreachable. The handler gets ownership at 1,
// irrespective of the normal postcondition of the abandoned continuation.
fn skipped_write (r:ref int)
  requires R.pts_to r 0
  ensures R.pts_to r 99
  raises (fun (e:nat) -> R.pts_to r 1 ** pure (e == 1))
{
  r := 1;
  raise 1;
  r := 99;
}

// A stateful payload expression is evaluated before transferring control.
fn raise_read (r:ref nat)
  requires R.pts_to r 7
  ensures pure False
  raises (fun (e:nat) -> R.pts_to r 7 ** pure (e == 7))
{
  raise (!r)
}

// The existing return label remains a normal exit inside a raises function.
fn early_return (b:bool)
  returns x:int
  ensures pure (b /\ x == 7)
  raises (fun (e:nat) -> pure (not b /\ e == 1))
{
  if (b) { return 7 }
  else { raise 1 }
}

// A local function gets its own exception scope; calling it propagates through
// its declared contract rather than jumping across a function boundary.
fn locally_defined (b:bool)
  returns x:int
  ensures pure (not b /\ x == 7)
  raises (fun (e:nat) -> pure (b /\ e == 1))
{
  fn local (b:bool)
    returns x:int
    ensures pure (not b /\ x == 7)
    raises (fun (e:nat) -> pure (b /\ e == 1))
  {
    if (b) { raise 1 }
    else { 7 }
  };
  local b
}
