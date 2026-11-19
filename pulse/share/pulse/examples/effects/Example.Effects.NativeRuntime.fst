module Example.Effects.NativeRuntime
#lang-pulse

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module N = Example.Effects.Native
module X = Example.Effects.NativeExtraction
module E = Pulse.Lib.Effects.Rules
module H = Example.Effects.NativeStress

fn early (b:bool)
  returns x:int
  ensures pure (b /\ x == 7)
  raises (fun (e:int) -> pure (not b /\ e == 9))
{
  if (b) { return 7 } else { raise 9 }
}

fn cleanup (b:bool)
  returns x:int
  ensures pure (not b /\ x == 7)
  raises (fun (e:int) -> pure (b /\ e == 9))
{
  let box = B.alloc 0;
  defer (B.pts_to box 0) { B.free box };
  if (b) { raise 9 } else { 7 }
}

fn cleanup_return ()
  returns x:int
  ensures pure (x == 7)
  raises (fun (_:int) -> pure False)
{
  let box = B.alloc 0;
  defer (B.pts_to box 0) { B.free box };
  return 7
}

fn return_through_try ()
  returns x:int
  ensures pure (x == 7)
{
  try
    returns x:int
    ensures pure (x == 7)
    raises (fun (_:int) -> pure False)
  { return 7 }
  catch { _ -> { 99 } }
}

fn stack_payload (s:string)
  returns x:string
  ensures pure False
  raises (fun (e:string) -> pure (e == s ^ s))
{
  let mut local = s ^ s;
  raise (!local)
}

fn return_payload (s:string)
  returns x:string
  ensures pure (x == s ^ s)
  raises (fun (_:string) -> pure False)
{
  return (s ^ s)
}

divergent fn cleanup_handles ()
  returns x:int
  ensures pure False
  raises (fun (e:int) -> pure (e == 9))
{
  let box = B.alloc 0;
  defer (B.pts_to box 0) {
    try
      ensures B.pts_to box 0
      raises (fun (e:bool) -> B.pts_to box 0 ** pure e)
    { raise true }
    catch { true -> { () } };
    while (true)
      invariant B.pts_to box 0
      ensures True
    { break };
    B.free box;
  };
  raise 9
}

exception First of int
exception Second of string

fn reraises ()
  returns x:int
  ensures pure False
  raises (fun (e:exn) -> pure (e == Second "outer"))
{
  try
    returns x:int
    ensures pure False
    raises (fun (e:exn) -> pure (e == First 3))
  { raise (First 3) }
  catch { First _ -> { raise (Second "outer") } }
}

divergent fn rec recurse (n:nat)
  returns x:int
  ensures pure False
  raises (fun (e:int) -> pure (e == 9))
{
  if (n = 0) { raise 9 } else { recurse (n - 1) }
}

// One runtime observation per property; ensures clauses are not the oracle.
// Cleanup frees real allocations so Cherry's sanitizer run detects omission
// and duplication on normal, exceptional, and early-return exits.
divergent fn test ()
  returns ok:bool
  ensures pure ok
{
  let a = early true;
  let b = try
    returns x:int
    ensures pure (x == 9)
    raises (fun (e:int) -> pure (e == 9))
  { early false }
  catch { 9 -> { 9 } };
  let c = cleanup false;
  let d = try
    returns x:int
    ensures pure (x == 9)
    raises (fun (e:int) -> pure (e == 9))
  { cleanup true }
  catch { 9 -> { 9 } };
  let e = cleanup_return ();
  let f = return_through_try ();
  let g = try
    returns x:int
    ensures pure (x == 9)
    raises (fun (e:int) -> pure (e == 9))
  { cleanup_handles () }
  catch { 9 -> { 9 } };
  let h = try
    returns x:int
    ensures pure (x == 11)
    raises (fun (e:exn) -> pure (e == Second "outer"))
  { reraises () }
  catch { Second _ -> { 11 } };
  let i = try
    returns x:int
    ensures pure (x == 9)
    raises (fun (e:int) -> pure (e == 9))
  { recurse 5 }
  catch { 9 -> { 9 } };
  let j = N.invoke N.locally_defined false;
  let k = try
    returns x:int
    ensures pure (x == 1)
    raises (fun (e:nat) -> pure (e == 1))
  { N.invoke N.locally_defined true }
  catch { 1 -> { 1 } };
  let mut state = 0;
  let mut frame = 17;
  try
    ensures R.pts_to state 1 ** R.pts_to frame 17
    raises (fun (e:nat) -> R.pts_to state 1 ** R.pts_to frame 17 ** pure (e == 1))
  { N.loop_exit state }
  catch { 1 -> { () } };
  let l = !state;
  state := 0;
  let m = N.reraised state;
  let n = !state;
  let o = !frame;
  let p = try
    returns x:string
    ensures R.pts_to state 5 ** R.pts_to frame 17 ** pure (x == "ownedowned")
    raises (fun (e:string) ->
      R.pts_to state 5 ** R.pts_to frame 17 ** pure (e == "ownedowned"))
  { stack_payload "owned" }
  catch { value -> { value } };
  let q = return_payload "owned";
  let raw = X.raw_outcome true;
  let r = (match raw with | E.Normal _ -> false | E.Raised value -> value);
  let s = X.handled_bool true;
  let t = X.handled_bool false;
  (a = 7 && b = 9 && c = 7 && d = 9 && e = 7 &&
   f = 7 && g = 9 && h = 11 && i = 9 &&
   j = 7 && k = 1 && l = 1 && m = 50 && n = 5 && o = 17 &&
   p = "ownedowned" && q = "ownedowned" && r && s && not t)
}

divergent fn stress (note:H.observer)
  returns ok:bool
  ensures emp
{
  H.test note
}
