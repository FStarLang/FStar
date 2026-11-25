module Example.Effects.NativeAbi
#lang-pulse

(* Runtime regressions for the native calling convention. native_outcome is a
   transparent alias of outcome, so F* may unfold it or instantiate a type
   variable at it; the checker recognizes only its syntactic spelling. Every
   case below verifies, so each must also run as specified: native functions
   return ordinary outcome data, and host exceptions never leave the function
   that raised them. NativeRuntime.test observes each result. *)

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module E = Pulse.Lib.Effects.Rules

// An explicit native_outcome result without a raises clause is still split by
// callers; its constructed Normal value must reach them as a value.
fn constructed_normal ()
  returns v:E.native_outcome bool int
  ensures pure (v == E.Normal 5)
{
  E.Normal #bool #int 5
}

fn split_constructed ()
  returns x:int
  ensures pure (x == 5)
{
  constructed_normal ()
}

// Likewise a constructed Raised value propagates to a handler.
fn constructed_raised ()
  returns v:E.native_outcome int unit
  ensures E.exit_post (fun (_:unit) -> pure False) (fun (e:int) -> pure (e == 4)) v
{
  E.Raised #int #unit 4
}

fn catch_constructed ()
  returns x:int
  ensures pure (x == 4)
{
  try
    returns x:int
    ensures pure (x == 4)
    raises (fun (e:int) -> pure (e == 4))
  { constructed_raised (); 0 }
  catch { e -> { e } }
}

// A native function used where a raw outcome callback is expected.
fn thrower ()
  returns x:int
  ensures pure False
  raises (fun (e:int) -> pure (e == 3))
{
  raise 3
}

fn raw_consumer
  (f: unit -> stt (E.outcome int int) emp
         (fun v -> E.exit_post (fun (_:int) -> pure False) (fun (e:int) -> pure (e == 3)) v))
  returns r:int
  ensures pure (r == 3)
{
  let v = f ();
  match v {
    E.Normal x -> { unreachable () }
    E.Raised e -> { e }
  }
}

fn native_as_raw ()
  returns r:int
  ensures pure (r == 3)
{
  raw_consumer thrower
}

// A raw outcome function used where a native callback is expected.
fn raw_normal ()
  returns v:E.outcome bool int
  ensures E.exit_post (fun (x:int) -> pure (x == 5)) (fun (_:bool) -> pure False) v
{
  E.Normal #bool #int 5
}

fn native_consumer
  (f: unit -> stt (E.native_outcome bool int) emp
         (fun v -> E.exit_post (fun (x:int) -> pure (x == 5)) (fun (_:bool) -> pure False) v))
  returns r:int
  ensures pure (r == 5)
{
  f ()
}

fn raw_as_native ()
  returns r:int
  ensures pure (r == 5)
{
  native_consumer raw_normal
}

// A polymorphic intermediary does not split its callback's result. If the
// callback's exception unwound through it, apply's write would be skipped.
fn apply (#t:Type0) (#post:t -> slprop) (r:B.box int)
  (f: fn (_:unit) returns x:t ensures post x)
  requires B.pts_to r 0
  returns x:t
  ensures B.pts_to r 1 ** post x
{
  let x = f ();
  B.(r := 1);
  x
}

fn thrower_emp ()
  returns x:unit
  ensures pure False
  raises (fun (_:int) -> emp)
{
  raise 3
}

fn polymorphic_intermediary ()
  returns v:int
  ensures pure (v == 1)
{
  let r = B.alloc 0;
  try
    returns u:unit
    ensures B.pts_to r 1
    raises (fun (_:int) -> B.pts_to r 1)
  {
    apply #(E.native_outcome int unit) r thrower_emp
  }
  catch { _ -> { () } };
  let v = B.(!r);
  B.free r;
  v
}

// Ownership travels with the payload: the handler frees a box raised from a
// callee, so Cherry's sanitizer detects a lost or duplicated payload.
fn raise_box (v:int)
  returns u:unit
  ensures pure False
  raises (fun (b:B.box int) -> B.pts_to b v)
{
  let b = B.alloc v;
  raise b
}

fn owned_payload ()
  returns v:int
  ensures pure (v == 6)
{
  try
    returns v:int
    ensures pure (v == 6)
    raises (fun (b:B.box int) -> B.pts_to b 6)
  { raise_box 6; 0 }
  catch { b -> { let v = B.(!b); B.free b; v } }
}

// Raises from expression positions: the checker hoists each stateful
// subterm, so the raise must still skip everything after it.
fn pick (b:bool)
  returns x:int
  ensures pure (b /\ x == 1)
  raises (fun (e:int) -> pure (not b /\ e == 2))
{
  if b { 1 } else { raise 2 }
}

fn add (x y:int) returns z:int ensures pure (z == x + y) { x + y }

fn hoisted (r:B.box int)
  requires B.pts_to r 0
  returns x:int
  ensures B.pts_to r 0 ** pure (x == 2)
{
  try
    returns x:int
    ensures B.pts_to r 0 ** pure (x == 2)
    raises (fun (e:int) -> B.pts_to r 0 ** pure (e == 2))
  {
    let mut acc = pick true;
    acc := add (pick true) (pick false);
    B.(r := 5);
    !acc
  }
  catch { e -> { e } }
}

divergent fn raise_in_condition (r:B.box int)
  requires B.pts_to r 0
  returns x:int
  ensures B.pts_to r 0 ** pure (x == 2)
{
  try
    returns x:int
    ensures B.pts_to r 0 ** pure (x == 2)
    raises (fun (e:int) -> B.pts_to r 0 ** pure (e == 2))
  {
    while (pick false = 1)
      invariant B.pts_to r 0
    { () };
    B.(r := 5);
    0
  }
  catch { e -> { e } }
}

// A raise in an inner catch clause escapes to the outer try, even when the
// two payload types differ, and the inner protected continuation is skipped.
fn nested_payload_types (r:B.box int)
  requires B.pts_to r 0
  returns x:int
  ensures B.pts_to r 1 ** pure (x == 8)
{
  try
    returns x:int
    ensures B.pts_to r 1 ** pure (x == 8)
    raises (fun (e:int) -> B.pts_to r 1 ** pure (e == 8))
  {
    try
      returns x:int
      ensures B.pts_to r 1 ** pure False
      raises (fun (b:bool) -> B.pts_to r 0 ** pure (b == true))
    { raise true; 0 }
    catch { b -> { B.(r := 1); raise 8 } }
  }
  catch { e -> { e } }
}

divergent fn test ()
  returns ok:bool
  ensures pure ok
{
  let a = split_constructed ();
  let b = catch_constructed ();
  let c = native_as_raw ();
  let d = raw_as_native ();
  let e = polymorphic_intermediary ();
  let f = owned_payload ();
  let r = B.alloc 0;
  let g = hoisted r;
  let h = raise_in_condition r;
  let i = nested_payload_types r;
  let j = B.(!r);
  B.free r;
  (a = 5 && b = 4 && c = 3 && d = 5 && e = 1 && f = 6 &&
   g = 2 && h = 2 && i = 8 && j = 1)
}
