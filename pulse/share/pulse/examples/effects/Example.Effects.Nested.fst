module Example.Effects.Nested
#lang-pulse

(* Two unit-payload exception layers, distinguished by tags. An inner throw
   recovers at state 2; an outer throw is forwarded and recovers at state 3.
   The handlers change the result type from empty to int to bool. *)

open Pulse.Lib.Pervasives
module E = Pulse.Lib.Effects.Core
module X = Pulse.Lib.Effects.Exception
module R = Pulse.Lib.Reference

let inner_pre (r:ref int) (b:bool) (_:unit) = R.pts_to r 0 ** pure b
let outer_pre (r:ref int) (b:bool) (_:unit) = R.pts_to r 0 ** pure (not b)
let outer_ops r b = X.extend E.empty_ops (outer_pre r b)

fn prepare_inner (r:ref int) (b:bool{b})
  requires R.pts_to r 0
  ensures inner_pre r b ()
{ fold (inner_pre r b ()) }

fn prepare_outer (r:ref int) (b:bool{not b})
  requires R.pts_to r 0
  ensures outer_pre r b ()
{ fold (outer_pre r b ()) }

let body (r:ref int) (b:bool)
  : X.prog (outer_ops r b) (inner_pre r b) E.Terminating
      E.empty (R.pts_to r 0) (fun _ -> emp) =
  if b then
    E.Step (fun () -> prepare_inner r b) (fun _ -> X.throw ())
  else
    E.Step (fun () -> prepare_outer r b)
      (fun _ -> E.Abort #_ #(X.extend (outer_ops r b) (inner_pre r b)) (X.Other X.Throw) ())

let inner_done (r:ref int) (b:bool) (n:int) =
  R.pts_to r 2 ** pure (b /\ n == 10)

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

let handle_inner (r:ref int) (b:bool)
  : X.prog E.empty_ops (outer_pre r b) E.Terminating
      int (R.pts_to r 0) (inner_done r b) =
  X.handle #_ #_ #_ #_ #E.Terminating #E.Terminating (body r b)
    (fun impossible -> match impossible with)
    (fun e -> E.lift (fun () -> inner_clause r b e))

let done_ (r:ref int) (b result:bool) =
  R.pts_to r (if b then 2 else 3) ** pure (result == b)

fn outer_return (r:ref int) (b:bool) (n:int)
  requires inner_done r b n
  returns result:bool
  ensures done_ r b result
{
  unfold (inner_done r b n);
  fold (done_ r b true);
  true
}

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

let handle_outer (r:ref int) (b:bool)
  : E.tree E.empty_ops E.Terminating bool (R.pts_to r 0) (done_ r b) =
  X.handle #_ #_ #_ #_ #E.Terminating #E.Terminating (handle_inner r b)
    (fun n -> E.lift (fun () -> outer_return r b n))
    (fun e -> E.lift (fun () -> outer_clause r b e))

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
