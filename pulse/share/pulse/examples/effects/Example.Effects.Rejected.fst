module Example.Effects.Rejected
#lang-pulse

open Pulse.Lib.Pervasives
module E = Pulse.Lib.Effects.Core
module X = Pulse.Lib.Effects.Exception
module R = Pulse.Lib.Reference
module C = Example.Effects.Graded
module Ops = Example.Effects.Core
module Ex = Example.Effects.Exception

let abort_pre (r:ref int) (_:unit) : slprop = R.pts_to r 0

// Abort has no private frame in which to hide this second cell.
[@@expect_failure [19]]
let stranded_abort_frame (r s:ref int)
  : X.prog E.empty_ops (abort_pre r)
      E.Terminating int (R.pts_to r 0 ** R.pts_to s 1) (fun _ -> emp) =
  X.throw #E.empty #unit #E.empty_ops #(abort_pre r)
    #E.Terminating #int #(fun _ -> emp) ()

// An abort cannot be smuggled through the returning-operation constructor.
[@@expect_failure [19]]
let abort_as_perform (r:ref int) =
  E.perform #(X.tag E.empty)
    #(X.extend E.empty_ops (fun (_:unit) -> R.pts_to r 0))
    #E.Terminating X.Throw ()

[@@expect_failure [19]]
let returning_as_abort (r:ref int)
  : E.tree (C.exchange_ops r) E.Terminating int (R.pts_to r 0) (fun _ -> emp) =
  E.Abort #unit #(C.exchange_ops r) () ()

[@@expect_failure [19]]
let downgrade_divergent_step (r:ref int) =
  E.weaken_grade E.Terminating (C.mixed_steps r true)

// Tree construction terminates, but its implementation may not.
[@@expect_failure [12]]
let ignore_implementation_grade (r:ref int)
  : stt int (R.pts_to r 0) (fun n -> C.exchange_post r n) =
  C.divergent_implementation r true

// Framing a nested tree strengthens the outer exit as well as the inner one.
[@@expect_failure [19]]
let forget_outer_frame (r s:ref int) (b:bool)
  : X.prog E.empty_ops (C.outer_pre r b) E.Terminating
      int (R.pts_to r 0 ** R.pts_to s 1) (C.inner_done r s b) =
  C.handle_inner r s b

[@@expect_failure [12]]
let ignore_handler_grade (r:ref int)
  : E.tree E.empty_ops E.Terminating int (R.pts_to r 0) (C.exchange_post r) =
  C.divergent_handler r true

// Ownership acquired by an embedded action is subject to the same rule.
let no_resources (_:unit) : slprop = emp

[@@expect_failure [19]]
let lose_acquired_resource
  (allocate:unit -> stt (ref int) emp (fun s -> R.pts_to s 0))
  : X.prog E.empty_ops no_resources E.Terminating int emp (fun _ -> emp) =
  E.Step allocate (fun _ ->
    X.throw #E.empty #unit #E.empty_ops #no_resources #E.Terminating #int
      #(fun _ -> emp) ())

[@@expect_failure [19]]
let stale_ownership (r:ref int)
  : E.tree (Ops.ops r) E.Terminating int (R.pts_to r 0)
      (fun n -> R.pts_to r 0 ** pure (n == 0)) =
  E.bind (E.perform #Ops.op #(Ops.ops r) #E.Terminating Ops.Exchange (hide 0, 1))
    (fun _ -> E.lift (fun () -> Ops.read_initial r))

[@@expect_failure [228]]
fn missing_request_ownership (r:ref int)
  returns n:int
  ensures R.pts_to r 2 ** pure (n == 42)
{
  E.run_terminating #Ops.op #(Ops.ops r) (Ops.exchange r) (Ops.client r)
}

[@@expect_failure [12]]
let unhandled_exception (r:ref int)
  : E.tree Ex.empty_ops E.Terminating int (R.pts_to r 0) (Ex.normal r true) =
  Ex.body r true

[@@expect_failure [19]]
fn wrong_exception_state (r:ref int)
  requires Ex.exceptional r true Ex.Boom
  ensures R.pts_to r 1
{
  unfold (Ex.exceptional r true Ex.Boom);
  let n = !r;
  assert pure (n == 0);
}
