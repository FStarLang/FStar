module Example.Effects.Graded
#lang-pulse

open Pulse.Lib.Pervasives
module E = Pulse.Lib.Effects.Core
module X = Pulse.Lib.Effects.Exception
module R = Pulse.Lib.Reference
module Rules = Pulse.Lib.Effects.Rules

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

// Routing is by layer, although both payload types are unit.
let body (r:ref int) (b:bool)
  : X.prog (outer_ops r b) (inner_pre r b) E.Terminating
      E.empty (R.pts_to r 0) (fun _ -> emp) =
  if b then
    E.Step (fun () -> prepare_inner r b) (fun _ -> X.throw ())
  else
    E.Step (fun () -> prepare_outer r b)
      (fun _ -> E.Abort #_ #(X.extend (outer_ops r b) (inner_pre r b)) (X.Other X.Throw) ())

let inner_done (r s:ref int) (b:bool) (n:int) =
  R.pts_to r 2 ** R.pts_to s 2 ** pure (b /\ n == 10)

fn inner_clause (r s:ref int) (b:bool) (_:unit)
  requires inner_pre r b () ** R.pts_to s 1
  returns n:int
  ensures inner_done r s b n
{
  unfold (inner_pre r b ());
  r := 2;
  s := 2;
  fold (inner_done r s b 10);
  10
}

let handle_inner (r s:ref int) (b:bool)
  : X.prog (E.frame_signature (R.pts_to s 1) E.empty_ops)
      (fun e -> outer_pre r b e ** R.pts_to s 1) E.Terminating
      int (R.pts_to r 0 ** R.pts_to s 1) (inner_done r s b) =
  let framed = X.frame (R.pts_to s 1) (body r b) in
  X.framed_layer (R.pts_to s 1)
    (X.handle #_ #_ #_ #_ #E.Terminating #E.Terminating framed
      (fun impossible -> match impossible with)
      (fun e -> E.lift (fun () -> inner_clause r s b e)))

let done_ (r s:ref int) (b result:bool) =
  R.pts_to r (if b then 2 else 3) **
  R.pts_to s (if b then 2 else 3) ** pure (result == b)

fn outer_return (r s:ref int) (b:bool) (n:int)
  requires inner_done r s b n
  returns result:bool
  ensures done_ r s b result
{
  unfold (inner_done r s b n);
  fold (done_ r s b true);
  true
}

fn outer_clause (r s:ref int) (b:bool) (_:unit)
  requires outer_pre r b () ** R.pts_to s 1
  returns result:bool
  ensures done_ r s b result
{
  unfold (outer_pre r b ());
  r := 3;
  s := 3;
  fold (done_ r s b false);
  false
}

fn nested_frame (choose_inner:bool)
  returns result:bool & (int & int)
  ensures pure (result == (choose_inner,
    ((if choose_inner then 2 else 3), (if choose_inner then 2 else 3))))
{
  let mut r = 0;
  let mut s = 1;
  let c = X.handle #_ #_ #_ #_ #E.Terminating #E.Terminating
    (handle_inner r s choose_inner)
    (fun n -> E.lift (fun () -> outer_return r s choose_inner n))
    (fun e -> E.lift (fun () -> outer_clause r s choose_inner e));
  let result = E.run_closed c;
  unfold (done_ r s choose_inner result);
  let rv = !r;
  let sv = !s;
  (result, (rv, sv))
}

// Returning operations keep a frame privately rather than giving it to the
// implementation. The operation itself transfers r from 0 to 1.
let exchange_post (r:ref int) (n:int) = R.pts_to r 1 ** pure (n == 10)
let exchange_ops (r:ref int) : E.signature unit =
  fun _ -> E.Returning unit int (fun _ -> R.pts_to r 0) (fun _ -> exchange_post r)

fn exchange (r:ref int) (_:unit)
  requires R.pts_to r 0
  returns n:int
  ensures exchange_post r n
{
  r := 1;
  fold (exchange_post r 10);
  10
}

let exchange_framed (r s:ref int)
  : stt int (R.pts_to r 0 ** R.pts_to s 5)
      (fun n -> exchange_post r n ** R.pts_to s 5) =
  let c = E.frame (R.pts_to s 5)
    (E.perform #unit #(exchange_ops r) #E.Terminating () ()) in
  let scoped = X.weaken #unit #E.empty
    #(E.frame_signature (R.pts_to s 5) (exchange_ops r))
    #(fun impossible -> match impossible with) c in
  let handled = X.handle #_ #_ #_ #_ #E.Terminating #E.Terminating scoped
    (fun n -> E.Return n) (fun impossible -> match impossible with) in
  E.run #_ #_ #E.Terminating #E.Terminating
    (fun _ arg -> exchange r arg)
    handled

fn returning_frame ()
  returns result:int & (int & int)
  ensures pure (result == (10, (1, 5)))
{
  let mut r = 0;
  let mut s = 5;
  let n = exchange_framed r s;
  unfold (exchange_post r n);
  let rv = !r;
  let sv = !s;
  (n, (rv, sv))
}

divergent fn rec exchange_maybe_diverges (r:ref int) (loop:bool) (_:unit)
  requires R.pts_to r 0
  returns n:int
  ensures exchange_post r n
{
  if loop { exchange_maybe_diverges r loop () }
  else { exchange r () }
}

// A terminating request tree does not imply a terminating interpretation.
let divergent_implementation (r:ref int) (loop:bool)
  : stt_div int (R.pts_to r 0) (fun n -> exchange_post r n) =
  E.run #unit #(exchange_ops r) #E.Terminating #E.MayDiverge
    (fun _ arg -> exchange_maybe_diverges r loop arg)
    (E.perform #unit #(exchange_ops r) #E.Terminating () ())

let mixed_steps (r:ref int) (loop:bool)
  : E.tree E.empty_ops E.MayDiverge int (R.pts_to r 0) (exchange_post r) =
  E.bind
    (E.Return #E.empty #E.empty_ops #E.Terminating #unit #(fun _ -> R.pts_to r 0) ())
    (fun _ -> E.lift #E.empty #E.empty_ops #E.MayDiverge
      (fun () -> exchange_maybe_diverges r loop ()))

let divergent_handler (r:ref int) (loop:bool)
  : E.tree E.empty_ops E.MayDiverge int (R.pts_to r 0) (exchange_post r) =
  X.handle #E.empty #unit #E.empty_ops #(fun _ -> R.pts_to r 0)
    #E.Terminating #E.MayDiverge #E.empty #int
    #(R.pts_to r 0) #(fun _ -> emp) #(exchange_post r)
    (X.throw ())
    (fun impossible -> match impossible with)
    (fun _ -> E.lift (fun () -> exchange_maybe_diverges r loop ()))

divergent fn mixed_grade_execution (loop:bool)
  returns result:int & int
  ensures pure (result == (10, 1))
{
  let mut r = 0;
  let n = E.run_closed_div (mixed_steps r loop);
  unfold (exchange_post r n);
  let rv = !r;
  (n, rv)
}

let normal_post (r:ref int) (b:bool) (x:int) =
  R.pts_to r 1 ** pure (b /\ x == 10)
let exceptional_post (r:ref int) (b:bool) (e:int) =
  R.pts_to r 1 ** pure (not b /\ e == 7)

fn raw_callback (r:ref int) (b:bool)
  requires R.pts_to r 0
  returns v:Rules.outcome int int
  ensures Rules.exit_post (normal_post r b) (exceptional_post r b) v
{
  r := 1;
  if b {
    fold (normal_post r b 10);
    Rules.Normal 10
  } else {
    fold (exceptional_post r b 7);
    Rules.Raised 7
  }
}

// The arbitrary-callback bridge preserves the selected exit, payload/result,
// and heap update. Both branches go through the tree interpreter.
fn outcome_round_trip (b:bool)
  returns result:bool & (int & int)
  ensures pure (result == (b, ((if b then 10 else 7), 1)))
{
  let mut r = 0;
  let c = Rules.of_outcome #E.empty #int #E.empty_ops
    #(exceptional_post r b) #E.Terminating #int #(R.pts_to r 0) #(normal_post r b)
    (fun () -> raw_callback r b);
  let v = Rules.run_tree c;
  match v {
    Rules.Normal x -> {
      unfold (normal_post r b x);
      let rv = !r;
      (true, (x, rv))
    }
    Rules.Raised e -> {
      unfold (exceptional_post r b e);
      let rv = !r;
      (false, (e, rv))
    }
  }
}
