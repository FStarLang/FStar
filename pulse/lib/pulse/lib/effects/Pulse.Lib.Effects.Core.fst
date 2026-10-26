module Pulse.Lib.Effects.Core
#lang-pulse

(* Implementation of the resource-indexed core described in the interface.

   Pure tree transformations never run the Step thunks they rearrange. The
   small Pulse helpers below provide executable sequencing, framing, returns,
   and ghost entailments for the interpreter. Keeping these helpers as actual
   Pulse definitions also avoids extracting calls to semantic-only stt helpers.

   The implementation separates three obligations: construct correctly indexed
   trees, interpret them with the advertised resource transfers, and preserve
   structural request policies. Local ** equalities make the transports explicit;
   none of those proofs dispose of heap ownership. *)

open Pulse.Lib.Core
open Pulse.Main

// Realize Return as an executable Pulse computation. Ownership q x is already
// available and is preserved while returning x; no allocation or proof of q x
// is manufactured by this helper.
fn return_value (#a:Type0) (x:a) (#q:a -> slprop)
  requires q x
  returns y:a
  ensures q y
{
  x
}

// Run one thunk, then pass both its result and its postcondition to next.
// The interpreter uses this for both ordinary Step nodes and operation replies.
fn sequence (#a #b:Type0) (#p:slprop) (#q:a -> slprop) (#s:b -> slprop)
  (action:unit -> stt a p (fun x -> q x))
  (next:(x:a -> stt b (q x) (fun y -> s y)))
  requires p
  returns y:b
  ensures s y
{
  let x = action ();
  next x
}

// Exercise Pulse's frame rule at the execution boundary: action consumes p,
// not f, and its returned resources are recombined with the unchanged f.
fn framed_action (#a:Type0) (#p:slprop) (#q:a -> slprop)
  (f:slprop) (action:unit -> stt a p (fun x -> q x))
  requires p ** f
  returns x:a
  ensures q x ** f
{
  action ()
}

// Store the action and immediately return its eventual result. The constructor
// application itself is pure; sequence is what will later invoke the thunk.
let lift #tag #ops #a #p #q action =
  Step action (fun x -> Return x)

// Equality transport has no operational content. Keeping the returned tree
// equal to c also lets policy proofs survive precondition rearrangements.
let reindex_pre #tag #ops #a #p #q p' pf c = c

// Replace normal leaves with next. Requests keep their tags/arguments/frames,
// and all continuations are composed recursively rather than executed here.
let rec bind #tag #ops #a #b #p #q #s c next =
  match c with
  | Return x -> next x
  | Step action k -> Step action (fun x -> bind (k x) next)
  | Perform op arg k -> Perform op arg (fun y -> bind (k y) next)

// Frame each executable action and extend each request's private frame r to
// r ** f. The two transports in Perform only reassociate resources: they do
// not move f into the request/reply protocol visible to the implementation.
let rec frame #tag #ops #a #p #q f c =
  match c with
  | Return x -> Return x
  | Step action k ->
      Step (fun () -> framed_action f action) (fun x -> frame f (k x))
  | Perform #_ #_ #_ #_ #r op arg k ->
      let next y : prog ops a ((ops op).reply arg y ** (r ** f)) (fun x -> q x ** f) =
        star_assoc ((ops op).reply arg y) r f;
        reindex_pre ((ops op).reply arg y ** (r ** f)) () (frame f (k y))
      in
      star_assoc ((ops op).request arg) r f;
      reindex_pre (p ** f) () (Perform #_ #_ #_ #_ #(r ** f) op arg next)

// Build Perform followed by Return, then remove the administrative ** emp from
// its external precondition. The reply-side transport restores the constructor's
// required reply ** emp while preserving the actual reply ownership.
let perform #tag #ops op arg =
  let next y : prog ops (ops op).output ((ops op).reply arg y ** emp) ((ops op).reply arg) =
    star_comm ((ops op).reply arg y) emp;
    emp_unit ((ops op).reply arg y);
    reindex_pre ((ops op).reply arg y ** emp) () (Return y)
  in
  star_comm ((ops op).request arg) emp;
  emp_unit ((ops op).request arg);
  reindex_pre ((ops op).request arg) () (Perform #_ #_ #_ #_ #emp op arg next)

// Rebuild requests using embed; its contract equality justifies reusing their
// arguments, reply types, and resource indices. Delayed Pulse actions are shared.
let rec weaken #tag #other #ops #target #a #p #q embed c =
  match c with
  | Return x -> Return x
  | Step action k -> Step action (fun x -> weaken embed (k x))
  | Perform #_ #_ #_ #_ #r op arg k ->
      Perform #other #target #a #q #r (embed op) arg
        (fun y -> weaken #tag #other #ops #target embed (k y))

// Package a verified ghost entailment as a Pulse action acceptable to Step.
// It changes logical ownership according to proof, not by running a heap update.
fn ghost_step (#p #q:slprop)
  (proof:unit -> stt_ghost unit emp_inames p (fun _ -> q))
  requires p
  ensures q
{
  proof ();
}

// Prepend the precondition entailment and append the result-indexed postcondition
// entailment. The final Return deliberately returns c's original result x.
let consequence #tag #ops #a #p #p' #q #q' before c after =
  Step (fun () -> ghost_step before)
    (fun _ -> bind c (fun x ->
      Step (fun () -> ghost_step (fun () -> after x)) (fun _ -> Return x)))

// The three constructor cases realize the interface's Hoare contract. In the
// operation case, framed_action shields the request's private frame from impl;
// sequence then gives the reply and retained frame to the recursive execution.
let rec run #tag #ops #a #p #q impl c =
  match c with
  | Return x -> return_value x
  | Step action k ->
      sequence action (fun x -> run impl (k x))
  | Perform op arg k ->
      sequence (fun () -> framed_action _ (fun () -> impl op arg))
        (fun y -> run impl (k y))

// Supply the unique implementation table on an empty tag type. Its impossible
// branch cannot execute, so this is a checked closing boundary, not a fallback.
let run_closed #ops #a #p #q c =
  run (fun op -> match op with) c

// Unfolding lift reveals a Step whose continuations are all Return.
let lift_all_requests #tag #ops #a #p #q action policy = ()

// The premise is precisely the Step clause of all_requests.
let step_all_requests #tag #ops #a #b #p #s #q action next policy = ()

// The interface's emp-frame premise discharges the sole request; transports
// preserve tree equality and the reply continuation is just Return.
let perform_all_requests #tag #ops op arg policy = ()

// Structural induction follows bind. Quantifier introduction supplies the
// induction hypothesis for every delayed action result and every operation reply.
let rec bind_all_requests #tag #ops #a #b #p #q #s c next policy =
  match c with
  | Return _ -> ()
  | Step action k ->
      FStar.Classical.forall_intro (fun x -> bind_all_requests (k x) next policy)
  | Perform op arg k ->
      FStar.Classical.forall_intro (fun y -> bind_all_requests (k y) next policy)

// Structural induction follows relabelling. The caller's uniform permission
// premise covers each embedded request, regardless of its retained frame.
let rec weaken_all_requests #tag #other #ops #target #a #p #q embed c policy =
  match c with
  | Return _ -> ()
  | Step action k ->
      FStar.Classical.forall_intro (fun x -> weaken_all_requests embed (k x) policy)
  | Perform op arg k ->
      FStar.Classical.forall_intro (fun y -> weaken_all_requests embed (k y) policy)
