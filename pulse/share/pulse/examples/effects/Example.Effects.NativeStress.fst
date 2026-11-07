module Example.Effects.NativeStress
#lang-pulse

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module U32 = FStar.UInt32
module L = Example.Effects.NativeBoundary

// The driver owns the observation log, outside the Pulse heap. No axiom or
// discarded permission is needed: tests take an ordinary emp-to-emp callback.
let observer = tag:U32.t -> stt unit emp (fun _ -> emp)

// Deliberately collides with the carrier's short name. A separately compiled
// library's exception identity and spelling must not depend on client names.
exception NativeException of string

fn collision ()
  returns result:string
  ensures pure False
  raises (fun (e:exn) -> pure (e == NativeException "collision"))
{
  raise (NativeException "collision")
}

fn nested (note:observer) (mode:nat)
  returns result:int
  ensures pure (mode < 2 /\ result == 7)
  raises (fun (e:int) -> pure (mode >= 2 /\ e == 9))
{
  let outer = B.alloc "outer";
  defer (B.pts_to outer "outer") { note 1ul; B.free outer };
  let inner = B.alloc "inner";
  defer (B.pts_to inner "inner") { note 2ul; B.free inner };
  if (mode = 0) { 7 }
  else if (mode = 1) { return 7 }
  else { raise 9 }
}

divergent fn loop_exits (note:observer)
  returns result:int
  ensures emp
  raises (fun (_:bool) -> pure False)
{
  let mut i = 0;
  while (true)
    invariant exists* k. R.pts_to i k
    ensures True
  {
    let k = !i;
    try
      ensures exists* k. R.pts_to i k
      raises (fun (_:bool) -> pure False)
    {
      defer emp { note 5ul };
      let box = B.alloc k;
      defer (B.pts_to box k) {
        note (if k = 0 then 3ul else 4ul);
        B.free box
      };
      if (k = 0) { i := 1; continue } else { break }
    }
    catch { _ -> { note 99ul } }
  };
  !i
}

fn return_handled (note:observer)
  returns result:int
  ensures pure (result == 7)
{
  defer emp { note 7ul };
  try
    returns result:int
    ensures pure (result == 7)
    raises (fun (_:bool) -> pure False)
  {
    defer emp { note 8ul };
    return 7
  }
  catch { _ -> { 99 } }
}

// Non-tail recursion: every frame owns a box containing a managed string list.
// The ascending trace on unwind distinguishes cleanup from call-entry order.
divergent fn rec unwind (note:observer) (n:nat{n <= 256}) (seed:string)
  returns result:int
  ensures pure False
  raises (fun (e:int) -> pure (e == 9))
{
  let contents = [seed ^ seed; seed];
  let box = B.alloc contents;
  defer (B.pts_to box contents) { note (U32.uint_to_t n); B.free box };
  if (n = 0) { raise 9 } else { unwind note (n - 1) seed }
}

fn captured (value:L.payload)
  returns ok:bool
  ensures emp
{
  let mut state = 0;
  let mut frame = 17;
  fn action ()
    requires R.pts_to state 0
    returns result:int
    ensures pure False
    raises (fun (e:L.payload) -> R.pts_to state 1 ** pure (e == value))
  { state := 1; raise value };
  let got = try
    returns result:L.payload
    ensures R.pts_to state 1 ** R.pts_to frame 17 ** pure (result == value)
    raises (fun (e:L.payload) ->
      R.pts_to state 1 ** R.pts_to frame 17 ** pure (e == value))
  {
    let _ = L.invoke state value action;
    value
  }
  catch { e -> { e } };
  let s = !state;
  let f = !frame;
  (s = 1 && f = 17 && got.L.message = value.L.message &&
   got.L.values = value.L.values)
}

divergent fn repeated (note:observer) (value:L.payload)
  returns ok:bool
  ensures emp
{
  let mut count = 0;
  let mut good = true;
  while (!count < 1000)
    invariant exists* n b. R.pts_to count n ** R.pts_to good b
  {
    let got = try
      returns result:L.payload
      ensures (exists* n b. R.pts_to count n ** R.pts_to good b) **
        pure (result == value)
      raises (fun (e:L.payload) ->
        (exists* n b. R.pts_to count n ** R.pts_to good b) ** pure (e == value))
    {
      let box = B.alloc value;
      defer (B.pts_to box value) { note 6ul; B.free box };
      L.deliver value true
    }
    catch { e -> { e } };
    good := (!good && got.L.message = value.L.message &&
             got.L.values = value.L.values);
    count := (!count + 1)
  };
  !good
}

// Driver assertions check both this result and an independently specified
// trace. Neither oracle is erased with the proof annotations.
divergent fn test (note:observer)
  returns ok:bool
  ensures emp
{
  note 100ul;
  let a = nested note 0;
  note 101ul;
  let b = nested note 1;
  note 102ul;
  let c = try
    returns result:int
    ensures pure (result == 9)
    raises (fun (e:int) -> pure (e == 9))
  { nested note 2 }
  catch { e -> { e } };
  note 200ul;
  let d = loop_exits note;
  note 201ul;
  let returned = return_handled note;
  note 300ul;
  let e = try
    returns result:int
    ensures pure (result == 9)
    raises (fun (e:int) -> pure (e == 9))
  { unwind note 256 "managed" }
  catch { e -> { e } };
  let value = { L.message = "managed" ^ "payload"; L.values = [3; 5; 8] };
  let f = L.deliver value false;
  let text = L.choose "polymorphic" false;
  let number = try
    returns result:int
    ensures pure (result == 37)
    raises (fun (e:int) -> pure (e == 37))
  { L.choose 37 true }
  catch { e -> { e } };
  let g = captured value;
  let name = try
    returns result:string
    ensures pure (result == "collision")
    raises (fun (e:exn) -> pure (e == NativeException "collision"))
  { collision () }
  catch { NativeException message -> { message } };
  note 400ul;
  let h = repeated note value;
  (a = 7 && b = 7 && c = 9 && d = 1 && returned = 7 && e = 9 &&
   f.L.message = "managedpayload" && f.L.values = [3; 5; 8] &&
   text = "polymorphic" && number = 37 && g && name = "collision" && h)
}
