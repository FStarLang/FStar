module Pulse.Lib.Effects.Exception
#lang-pulse

(* Abortive exception handling over the common resource-indexed core.

   An exception is an operation with no reply value. Handling replaces a local
   Throw with an exceptional clause and does not run its continuation; unrelated
   operations are forwarded with their continuations still under the handler.
   Clauses may change both the result type and the final ownership assertion.

   handle and catch have the same abortive control behavior, but different
   ownership interfaces. handle exposes an arbitrary abandoned private frame
   to a frame-polymorphic clause. catch restricts the input tree so every local
   Throw has an empty private frame, making a clause over exceptional e enough.
   Neither API implicitly frees resources or offers resumable continuations.
   See README.md for why the frame restriction matters and how layers compose. *)

open Pulse.Lib.Core
// E provides the shared tree, operation contracts, and structural policy proofs.
module E = Pulse.Lib.Effects.Core

// Extend an existing tag space by one distinguished local exception operation.
// Nested applications distinguish exception layers even with identical payloads.
type tag (other:Type0) =
  // The exception belonging to this layer; it is consumed by this layer's catch.
  | Throw
  // An operation belonging to an enclosing environment; forward it unchanged.
  | Other : other -> tag other

// Give Throw the request ownership exceptional e and the uninhabited reply type.
// Its nominal emp reply assertion is never realized by a reply value. Existing
// operations retain their original request/reply contracts under Other.
let extend (#other:Type0) (#exn:Type0)
  (ops:E.signature other) (exceptional:exn -> slprop)
  : E.signature (tag other) = function
  | Throw -> {
      E.input = exn;
      E.output = E.empty;
      E.request = exceptional;
      E.reply = (fun _ _ -> emp);
    }
  | Other op -> ops op

// The local resource-conservation discipline: a Throw cannot strand ownership
// outside exceptional e. Other requests are unrestricted by this local policy;
// an enclosing exception layer may separately constrain some of them.
let frame_policy (#other #exn:Type0)
  (ops:E.signature other) (exceptional:exn -> slprop)
  : E.request_policy (extend ops exceptional) =
  fun op _ frame -> match op with
    | Throw -> frame == emp
    | Other _ -> True

// Require the local frame discipline throughout every continuation of c.
// This predicate describes the tree; it neither captures nor transfers resources
// by itself. Actual transfers occur when the interpreted operations execute.
let transfers_frame (#other #exn #a:Type0)
  (#ops:E.signature other) (#exceptional:exn -> slprop)
  (#p:slprop) (#q:a -> slprop)
  (c:E.prog (extend ops exceptional) a p q)
  : prop = E.all_requests c (frame_policy ops exceptional)

// All resources at an abort site must be in its exceptional contract,
// not stranded in the discarded continuation. Core.frame adds ownership to
// continuation frames: frame a handled computation, or explicitly extend
// the exceptional contract, rather than expecting catch to recover that frame.
// The refinement is erased: it restricts which Core trees can use catch without
// introducing a second runtime representation.
type prog (#other #exn:Type0)
  (ops:E.signature other) (exceptional:exn -> slprop)
  (a:Type0) (p:slprop) (q:a -> slprop) =
  c:E.prog (extend ops exceptional) a p q{transfers_frame c}

// Lift an ordinary Pulse action into the disciplined exception fragment.
// There are no reified requests to violate the local empty-frame policy.
inline_for_extraction
val lift (#other #exn #a:Type0)
  (#ops:E.signature other) (#exceptional:exn -> slprop)
  (#p:slprop) (#q:a -> slprop)
  (action:unit -> stt a p (fun x -> q x))
  : prog ops exceptional a p q

// Sequence computations that both respect the local throw discipline. Normal
// completion supplies q x to next x; a local Throw bypasses next entirely.
// The implementation trims impossible throw continuations for extraction.
inline_for_extraction
val bind (#other #exn #a #b:Type0)
  (#ops:E.signature other) (#exceptional:exn -> slprop)
  (#p:slprop) (#q:a -> slprop) (#s:b -> slprop)
  (c:prog ops exceptional a p q)
  ([@@@FStar.Attributes.monomorphize] next:(x:a -> prog ops exceptional b (q x) s))
  : Tot (prog ops exceptional b p s) (decreases c)

// Raise e, transferring exactly exceptional e and retaining no private frame.
// The normal result type and postcondition are arbitrary because there can be
// no normal return; this does not require proving that arbitrary postcondition.
inline_for_extraction
val throw (#other #exn #a:Type0)
  (#ops:E.signature other) (#exceptional:exn -> slprop)
  (#q:a -> slprop) (e:exn)
  : prog ops exceptional a (exceptional e) q

// The abort clause takes ownership of both the request and the abandoned
// continuation's frame. The library does not dispose of either resource.
// This accepts a raw Core tree, but on_throw must work for every frame with the
// same final s. A usual clause that only handles exceptional e is insufficient:
// it would leave the arbitrary frame unaccounted for. This is the low-level
// resource-explicit variant, not a more general resumable control handler.
inline_for_extraction
val handle (#other #exn #a #b:Type0)
  (#ops:E.signature other) (#exceptional:exn -> slprop)
  (#p:slprop) (#q:a -> slprop) (#s:b -> slprop)
  (c:E.prog (extend ops exceptional) a p q)
  ([@@@FStar.Attributes.monomorphize] on_return:(x:a -> E.prog ops b (q x) s))
  ([@@@FStar.Attributes.monomorphize] on_throw:(#frame:slprop -> e:exn ->
    E.prog ops b (exceptional e ** frame) s))
  : Tot (E.prog ops b p s) (decreases c)

// The convenient abortive handler for the refined prog fragment. At a Throw,
// the refinement proves frame == emp, so on_throw owns just exceptional e.
// on_return and on_throw both establish s, possibly at a new result type b.
// Other requests are forwarded; neither clause runs under this removed layer.
inline_for_extraction
val catch (#other #exn #a #b:Type0)
  (#ops:E.signature other) (#exceptional:exn -> slprop)
  (#p:slprop) (#q:a -> slprop) (#s:b -> slprop)
  (c:prog ops exceptional a p q)
  ([@@@FStar.Attributes.monomorphize] on_return:(x:a -> E.prog ops b (q x) s))
  ([@@@FStar.Attributes.monomorphize] on_throw:(e:exn -> E.prog ops b (exceptional e) s))
  : Tot (E.prog ops b p s) (decreases c)

// Pull an enclosing environment's policy back through Other, while imposing
// nothing on the local Throw that will be removed. This is separate from the
// local frame policy: nested handling needs both facts about the input tree.
let forwarded_policy (#other #exn:Type0)
  (ops:E.signature other) (exceptional:exn -> slprop)
  (policy:E.request_policy ops) : E.request_policy (extend ops exceptional) =
  fun op arg frame -> match op with
    | Throw -> True
    | Other op -> policy op arg frame

// Show that catch preserves a policy on the surviving operations, provided
// the input's forwarded requests and both clauses satisfy it. In particular,
// an inner catch can produce a tree acceptable to an outer catch rather than
// losing the proof that outer exceptions also retain no private ownership.
val catch_all_requests (#other #exn #a #b:Type0)
  (#ops:E.signature other) (#exceptional:exn -> slprop)
  (#p:slprop) (#q:a -> slprop) (#s:b -> slprop)
  (c:prog ops exceptional a p q)
  (on_return:(x:a -> E.prog ops b (q x) s))
  (on_throw:(e:exn -> E.prog ops b (exceptional e) s))
  (policy:E.request_policy ops)
  : Lemma
      (requires
        E.all_requests c (forwarded_policy ops exceptional policy) /\
        (forall x. E.all_requests (on_return x) policy) /\
        (forall e. E.all_requests (on_throw e) policy))
      (ensures E.all_requests (catch c on_return on_throw) policy)
      (decreases c)

// Embed a Core computation as Other operations under a fresh exception layer.
// It cannot raise this layer's Throw, so the local refinement holds automatically.
// This does not establish any additional policy on the original operations.
inline_for_extraction
val weaken (#other #exn #a:Type0)
  (#ops:E.signature other) (#exceptional:exn -> slprop)
  (#p:slprop) (#q:a -> slprop)
  (c:E.prog ops a p q)
  : prog ops exceptional a p q
