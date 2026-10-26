module Pulse.Lib.Effects.Core
#lang-pulse

(* Resource-indexed computations with reified control and ordinary Pulse steps.

   This is the semantic interface for the first effects-library milestone.
   A program describes how execution transforms owned resources; constructing
   the description does not require or manipulate those resources. run realizes
   the description as a Pulse computation once its precondition is available.

   The central transfer rule is request ** frame -> reply ** frame. Operations
   receive only their request resources, while their continuations retain the
   private frame. The exception layer refines this rule for abortive handling.
   The guarantees here are interpreter Hoare contracts and structural policy
   preservation, not an observational-equivalence or monad-law development.

   Custard specializes the existentially typed Step representation. The current
   executable examples use specialized tree shapes; arbitrary runtime-shaped
   trees and owned, first-class resumptions are not established by this API.
   See README.md for the file map, build instructions, and ownership examples. *)

open Pulse.Lib.Core
open Pulse.Main

// The protocol for one operation, independent of any particular implementation.
// Result types depend on the operation tag, not on the input value; reply can
// relate both values and resources. Inputs may carry erased specification data.
noeq
type operation = {
  // Data supplied at a request site, including any ghost parameters.
  input: Type0;
  // Data supplied on resumption; empty makes an operation non-returning.
  output: Type0;
  // Ownership handed to the operation implementation or handling clause.
  request: input -> slprop;
  // Ownership and facts returned to the suspended continuation.
  reply: input -> output -> slprop;
}

// A statically typed effect environment. Tags select complete operation
// protocols; sums of tag types can extend an environment without changing prog.
let signature (tag:Type0) = tag -> operation

// An uninhabited tag type closes an environment. As an operation's output type,
// it also expresses that no resumption value can be supplied.
type empty =

// Intrinsically specified, inductively constructed code: prog ops a p q executes
// from p and returns an a satisfying q when interpreted with suitable handlers.
// This value is duplicable code, not a token owning p or a captured stack.
// Recursive combinators decrease on the tree, including continuation subtrees.
noeq
type prog (#tag:Type0) (ops:signature tag) (a:Type0)
  : slprop -> (a -> slprop) -> Type =
  // Terminate with x. No heap action establishes q x: it must already hold.
  | Return : #q:(a -> slprop) -> x:a -> prog ops a (q x) q
  // Delay a Pulse computation. Its result-dependent postcondition supplies
  // exactly the resources needed by next; merely building Step runs nothing.
  | Step : #p:slprop -> #q:(a -> slprop) ->
      #b:Type0 -> #s:(b -> slprop) ->
      action:(unit -> stt b p (fun x -> s x)) ->
      next:(x:b -> prog ops a (s x) q) ->
      prog ops a p q
  // Suspend at an operation request. Preserve frame separately from request;
  // resume only with a reply value and reply ownership, not the old request.
  | Perform : #q:(a -> slprop) -> #frame:slprop ->
      op:tag -> arg:(ops op).input ->
      next:(y:(ops op).output ->
        prog ops a ((ops op).reply arg y ** frame) q) ->
      prog ops a ((ops op).request arg ** frame) q

// An additional logical restriction on requests and their private frames.
// It does not change an operation's protocol or perform any runtime check.
// Exception.frame_policy uses this hook to prohibit stranded abort-site frames.
let request_policy (#tag:Type0) (ops:signature tag) =
  op:tag -> (ops op).input -> slprop -> prop

// Require policy throughout the tree, quantifying over every continuation
// argument, not just one concrete execution. Return has no requests; Step
// checks its continuations; Perform checks its own request and its continuations.
let rec all_requests (#tag:Type0) (#ops:signature tag) (#a:Type0)
  (#p:slprop) (#q:a -> slprop)
  (c:prog ops a p q) (policy:request_policy ops)
  : Tot prop (decreases c) =
  match c with
  | Return _ -> True
  | Step action k -> forall x. all_requests (k x) policy
  | Perform #_ #_ #_ #_ #r op arg k ->
      policy op arg r /\ (forall y. all_requests (k y) policy)

// Embed an ordinary Pulse action without executing it. This contributes a Step
// followed by Return, so it introduces no algebraic operation of its own.
inline_for_extraction
val lift (#tag:Type0) (#ops:signature tag) (#a:Type0)
  (#p:slprop) (#q:a -> slprop)
  (action:unit -> stt a p (fun x -> q x))
  : prog ops a p q

// Transport along equality of preconditions, preserving the very same tree.
// Useful for associativity/unit rearrangements of ** that elaboration does not
// automatically coerce. This is equality transport, not arbitrary entailment.
inline_for_extraction
val reindex_pre (#tag:Type0) (#ops:signature tag) (#a:Type0)
  (#p:slprop) (#q:a -> slprop) (p':slprop) (_:squash (p == p'))
  (c:prog ops a p q)
  : c':prog ops a p' q{c' == c}

// Sequence descriptions: each normal result x transfers q x to next x.
// Requests and delayed actions stay in order, with sequencing threaded through
// their continuations. Specializing next supports extraction of the composition.
inline_for_extraction
val bind (#tag:Type0) (#ops:signature tag) (#a #b:Type0)
  (#p:slprop) (#q:a -> slprop) (#s:b -> slprop)
  (c:prog ops a p q)
  ([@@@FStar.Attributes.monomorphize] next:(x:a -> prog ops b (q x) s))
  : Tot (prog ops b p s) (decreases c)

// Thread additional ownership f through every action and continuation without
// giving it to operation implementations. At a Perform node it joins the private
// frame. This can invalidate an exception layer's empty-abort-frame policy:
// frame the handled computation instead, or change its exceptional protocol.
inline_for_extraction
val frame (#tag:Type0) (#ops:signature tag) (#a:Type0)
  (#p:slprop) (#q:a -> slprop)
  (f:slprop) (c:prog ops a p q)
  : Tot (prog ops a (p ** f) (fun x -> q x ** f)) (decreases c)

// The minimal requesting program: issue op arg with an empty private frame,
// then return the reply value with precisely the reply postcondition.
inline_for_extraction
val perform (#tag:Type0) (#ops:signature tag)
  (op:tag) (arg:(ops op).input)
  : prog ops (ops op).output ((ops op).request arg) ((ops op).reply arg)

// Relabel all requests into target while preserving their complete protocols.
// Injectivity is not required for this safety statement, so this is not a
// theorem that distinct nominal operations remain distinguishable.
inline_for_extraction
val weaken (#tag #other:Type0)
  (#ops:signature tag) (#target:signature other) (#a:Type0)
  (#p:slprop) (#q:a -> slprop)
  (embed:(op:tag -> l:other{target l == ops op}))
  (c:prog ops a p q)
  : Tot (prog target a p q) (decreases c)

// Change the advertised pre/postconditions using verified ghost entailments.
// before turns p' into p; after turns each q x into q' x. These proof steps
// surround c without changing its returned value or adding algebraic requests.
inline_for_extraction
val consequence (#tag:Type0) (#ops:signature tag) (#a:Type0)
  (#p #p':slprop) (#q #q':a -> slprop)
  (before:unit -> stt_ghost unit emp_inames p' (fun _ -> p))
  (c:prog ops a p q)
  (after:(x:a -> stt_ghost unit emp_inames (q x) (fun _ -> q' x)))
  : prog ops a p' q'

// A returning Pulse implementation for every operation in an environment.
// Each obeys its own request/reply protocol, without access to private frames.
// This is not a general control handler: there is no resumption argument.
let implementations (#tag:Type0) (ops:signature tag) =
  op:tag -> arg:(ops op).input ->
    stt (ops op).output ((ops op).request arg) (fun y -> (ops op).reply arg y)

// Interpret Return/Step/Perform using their ownership contracts. The result
// is a Pulse computation from p to q; this type is the interpreter's soundness
// guarantee. At Perform, impl receives request and the continuation gets reply
// plus the retained frame. No operation is silently ignored.
val run (#tag:Type0) (#ops:signature tag) (#a:Type0)
  (#p:slprop) (#q:a -> slprop)
  (impl:implementations ops)
  (c:prog ops a p q)
  : Tot (stt a p (fun x -> q x)) (decreases c)

// Execute a description whose effect environment is empty. No implementation
// table is needed because a Perform tag cannot exist; unresolved exception or
// state-operation environments must be handled before using this entry point.
fn run_closed (#ops:signature empty) (#a:Type0)
  (#p:slprop) (#q:a -> slprop)
  (c:prog ops a p q)
  requires p
  returns x:a
  ensures q x

// A lifted Pulse action is vacuously acceptable under any request policy.
// The claim concerns reified requests, not the absence of ordinary heap effects.
val lift_all_requests (#tag:Type0) (#ops:signature tag) (#a:Type0)
  (#p:slprop) (#q:a -> slprop)
  (action:unit -> stt a p (fun x -> q x)) (policy:request_policy ops)
  : Lemma (all_requests (lift action) policy)

// Build the policy proof for a Step from proofs for all its continuations.
// Useful when composing policy-refined trees directly, as in the nested example.
val step_all_requests (#tag:Type0) (#ops:signature tag) (#a #b:Type0)
  (#p:slprop) (#s:b -> slprop) (#q:a -> slprop)
  (action:unit -> stt b p (fun x -> s x))
  (next:(x:b -> prog ops a (s x) q))
  (policy:request_policy ops)
  : Lemma (requires forall x. all_requests (next x) policy)
          (ensures all_requests (Step action next) policy)

// A minimal perform satisfies policy when that one request is allowed with emp.
// Its Return continuation introduces no further obligations.
val perform_all_requests (#tag:Type0) (#ops:signature tag)
  (op:tag) (arg:(ops op).input) (policy:request_policy ops)
  : Lemma (requires policy op arg emp)
          (ensures all_requests (perform op arg) policy)

// Sequencing preserves a policy shared by c and every possible next x.
// This exposes compositional reasoning without asking clients to unfold bind
// and quantify over its internal continuation functions themselves.
val bind_all_requests (#tag:Type0) (#ops:signature tag) (#a #b:Type0)
  (#p:slprop) (#q:a -> slprop) (#s:b -> slprop)
  (c:prog ops a p q) (next:(x:a -> prog ops b (q x) s))
  (policy:request_policy ops)
  : Lemma (requires all_requests c policy /\ (forall x. all_requests (next x) policy))
          (ensures all_requests (bind c next) policy)
          (decreases c)

// Establish a target policy when it permits every embedded request and frame.
// This deliberately strong premise suffices to embed a computation as Other
// operations under an exception layer, whose local throw restriction is vacuous.
// It is not a general theorem transporting an arbitrary source policy.
val weaken_all_requests (#tag #other:Type0)
  (#ops:signature tag) (#target:signature other) (#a:Type0)
  (#p:slprop) (#q:a -> slprop)
  (embed:(op:tag -> l:other{target l == ops op}))
  (c:prog ops a p q) (policy:request_policy target)
  : Lemma (requires forall op arg frame. policy (embed op) arg frame)
          (ensures all_requests (weaken embed c) policy)
          (decreases c)
