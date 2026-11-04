module Example.Effects.NativeExtraction
#lang-pulse

open Pulse.Lib.Pervasives
module E = Pulse.Lib.Effects.Rules

// The callee is assumed, not a Pulse body discoverable by extraction. Its
// native ABI must still rule out standalone C, even with no reachable raise.
assume val native_normal : unit -> stt (E.native_outcome bool bool) emp
  (fun v -> pure (v == E.Normal true))

fn implicit_call ()
  returns x:bool
  ensures pure x
{
  native_normal ()
}

// A scope without a raise still has the native ABI.
fn normal_scope ()
  returns x:bool
  ensures pure x
  raises (fun (_:bool) -> pure False)
{
  true
}

// No native result marker remains in this function's public signature. Its
// checked handler still requires an exception-capable extraction backend.
fn handled_bool (b:bool)
  returns x:bool
  ensures pure (x == b)
{
  try
    returns x:bool
    ensures pure (x == b)
    raises (fun (e:bool) -> pure (e == b))
  { if (b) { raise b } else { b } }
  catch { value -> { value } }
}

// Raw outcomes and ordinary early returns are still supported. Keep this in
// the same module as rejected entries to check demand-driven extraction.
fn raw_outcome (b:bool)
  returns x:E.outcome bool bool
  ensures pure (x == (if b then E.Raised true else E.Normal true))
{
  if (b) { return E.Raised true }
  else { E.Normal true }
}