module Pulse.Lib.Effects.Rules
#lang-pulse

(* Two-exit proof rules for native, abortive exceptions. Unlike Core.prog,
   this representation contains no reified computation tree: both exits are
   ordinary Pulse results. A checker can implement these rules directly.
   Exception payloads are parameterized, so their identity is not tied to a
   particular closed datatype or to F*'s host-language exceptions. *)

open Pulse.Lib.Core
open Pulse.Main
module R = Pulse.Lib.Reference

type outcome (exn a:Type0) =
  | Normal : value:a -> outcome exn a
  | Raised : payload:exn -> outcome exn a

// Reserved checker ABI: native raises contracts retain this transparent alias
// in their result type. Raw outcome computations remain ordinary library data.
type native_outcome (exn a:Type0) = outcome exn a

// The two exits transfer different resources. In particular, an impossible
// exceptional exit is pure False, not emp.
[@@pulse_unfold]
let exit_post (#exn #a:Type0) (q:a -> slprop) (r:exn -> slprop)
  (v:outcome exn a) : slprop =
  match v with
  | Normal x -> q x
  | Raised e -> r e

let no_exceptions (#exn:Type0) (_:exn) : slprop = pure False

unfold let stt_exn (exn a:Type0) (p:slprop) (q:a -> slprop) (r:exn -> slprop) =
  stt (outcome exn a) p (fun v -> exit_post q r v)

unfold let stt_exn_div (exn a:Type0) (p:slprop) (q:a -> slprop) (r:exn -> slprop) =
  stt_div (outcome exn a) p (fun v -> exit_post q r v)

// Returning and raising each require precisely the resources of that exit.
val return_ (#exn #a:Type0) (#q:a -> slprop) (#r:exn -> slprop) (x:a)
  : stt_exn exn a (q x) q r

val raise_ (#exn #a:Type0) (#q:a -> slprop) (#r:exn -> slprop) (e:exn)
  : stt_exn exn a (r e) q r

// Sequencing invokes next only on Normal. Both computations use the same
// exceptional contract; pointwise consequence can reconcile differing ones.
val bind (#exn #a #b:Type0) (#p:slprop)
  (#q:a -> slprop) (#s:b -> slprop) (#r:exn -> slprop)
  (action:unit -> stt_exn exn a p q r)
  (next:(x:a -> stt_exn exn b (q x) s r))
  : stt_exn exn b p s r

val bind_div (#exn #a #b:Type0) (#p:slprop)
  (#q:a -> slprop) (#s:b -> slprop) (#r:exn -> slprop)
  (action:unit -> stt_exn_div exn a p q r)
  (next:(x:a -> stt_exn_div exn b (q x) s r))
  : stt_exn_div exn b p s r

// A frame must survive BOTH exits, rather than being abandoned on a raise.
val frame (#exn #a:Type0) (#p:slprop)
  (#q:a -> slprop) (#r:exn -> slprop) (f:slprop)
  (action:unit -> stt_exn exn a p q r)
  : stt_exn exn a (p ** f) (fun x -> q x ** f) (fun e -> r e ** f)

val frame_div (#exn #a:Type0) (#p:slprop)
  (#q:a -> slprop) (#r:exn -> slprop) (f:slprop)
  (action:unit -> stt_exn_div exn a p q r)
  : stt_exn_div exn a (p ** f) (fun x -> q x ** f) (fun e -> r e ** f)

// Nonraising calls can be embedded without manufacturing an exceptional exit.
val lift (#exn #a:Type0) (#p:slprop) (#q:a -> slprop)
  (action:unit -> stt a p (fun x -> q x))
  : stt_exn exn a p q no_exceptions

val lift_div (#exn #a:Type0) (#p:slprop) (#q:a -> slprop)
  (action:unit -> stt_div a p (fun x -> q x))
  : stt_exn_div exn a p q no_exceptions

// Consequence discharges each exit separately using verified ghost entailments.
val consequence (#exn #a:Type0) (#p #p':slprop)
  (#q #q':a -> slprop) (#r #r':exn -> slprop)
  (before:unit -> stt_ghost unit emp_inames p' (fun _ -> p))
  (normal:(x:a -> stt_ghost unit emp_inames (q x) (fun _ -> q' x)))
  (exceptional:(e:exn -> stt_ghost unit emp_inames (r e) (fun _ -> r' e)))
  (action:unit -> stt_exn exn a p q r)
  : stt_exn exn a p' q' r'

val consequence_div (#exn #a:Type0) (#p #p':slprop)
  (#q #q':a -> slprop) (#r #r':exn -> slprop)
  (before:unit -> stt_ghost unit emp_inames p' (fun _ -> p))
  (normal:(x:a -> stt_ghost unit emp_inames (q x) (fun _ -> q' x)))
  (exceptional:(e:exn -> stt_ghost unit emp_inames (r e) (fun _ -> r' e)))
  (action:unit -> stt_exn_div exn a p q r)
  : stt_exn_div exn a p' q' r'

// Handling removes only exceptions selected by matches. The normal clause and
// caught clause execute outside the protected action and may themselves raise
// under outer. In particular, re-raising is ordinary use of raise_.
// Unmatched exceptions need a proof that their resources establish outer.
val handle (#exn #a #b:Type0) (#p:slprop)
  (#q:a -> slprop) (#r:exn -> slprop)
  (#s:b -> slprop) (#outer:exn -> slprop)
  (matches:exn -> bool)
  (action:unit -> stt_exn exn a p q r)
  (normal:(x:a -> stt_exn exn b (q x) s outer))
  (caught:(e:exn{matches e} -> stt_exn exn b (r e) s outer))
  (forward:(e:exn{not (matches e)} ->
    stt_ghost unit emp_inames (r e) (fun _ -> outer e)))
  : stt_exn exn b p s outer

val handle_div (#exn #a #b:Type0) (#p:slprop)
  (#q:a -> slprop) (#r:exn -> slprop)
  (#s:b -> slprop) (#outer:exn -> slprop)
  (matches:exn -> bool)
  (action:unit -> stt_exn_div exn a p q r)
  (normal:(x:a -> stt_exn_div exn b (q x) s outer))
  (caught:(e:exn{matches e} -> stt_exn_div exn b (r e) s outer))
  (forward:(e:exn{not (matches e)} ->
    stt_ghost unit emp_inames (r e) (fun _ -> outer e)))
  : stt_exn_div exn b p s outer

// The mask is a condition on payloads, never a test of slprop satisfiability.
let residual (#exn:Type0) (r:exn -> slprop) (matches:exn -> bool)
  (e:exn) : slprop = r e ** pure (not (matches e))

// Scope exit reclaims the local on either outcome. The public exceptional
// contract mentions no local; the body must return its ownership on both exits.
val with_local (#exn #a #t:Type0) (#p:slprop)
  (#q:a -> slprop) (#r:exn -> slprop) (init:t)
  (body:(local:R.ref t ->
    stt_exn exn a (p ** R.pts_to local init)
      (fun x -> q x ** R.pts_to_uninit local)
      (fun e -> r e ** R.pts_to_uninit local)))
  : stt_exn exn a p q r

val with_local_div (#exn #a #t:Type0) (#p:slprop)
  (#q:a -> slprop) (#r:exn -> slprop) (init:t)
  (body:(local:R.ref t ->
    stt_exn_div exn a (p ** R.pts_to local init)
      (fun x -> q x ** R.pts_to_uninit local)
      (fun e -> r e ** R.pts_to_uninit local)))
  : stt_exn_div exn a p q r
