module Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.CAS
#lang-pulse

(**
Cached-WaitFree big atomics, specialized to a two-word payload.

Algorithm: Daniel Anderson, Guy E. Blelloch, and Siddhartha Jayanti,
"Big Atomics", Algorithm 1, https://arxiv.org/abs/2501.07503.
Proof starting point: cmuparlay's Iris/Rocq development, CachedWaitFree.v,
https://github.com/cmuparlay/bigatomic-mechanization/blob/251ff8b71e0879f561c729115e972b7a6d3ce0af/theories/CachedWaitFree.v
The upstream MIT notice is preserved in LICENSE.Iris.

This preserves the reference's cas control flow: read once, try the sampled
tagged pointer, then try its unmarked form, and return false if both fail.
There is no reread loop and no spurious-failure weakening of value-CAS.
The hard case is A--B--A: neither failed pointer comparison need observe a
value unequal to A. Instead the A--B publication has already committed this
caller's failure continuation in the ghost registry, before A returns.

Registration and Attempt connect each physical access to that registry;
Registry ports the reference's cas_inv/registry_inv/linearize_cas reasoning.
Locality keeps arbitrary captured client state at its initiating locality.
The registry and helping traversal erase; there is no runtime announcement
array or additional helping loop. Immutable, one-use arena nodes stand in
for allocation, and natural-number counters exclude wraparound. Those
modeling choices and the native primitive boundary are detailed in README.md.
*)

open Pulse.Lib.Pervasives
module G = Pulse.Lib.GhostReference
module H = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Model
module N = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Storage
module P = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Registry
module Q = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.State
module R = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Read
module V = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Validate
module K = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Registration
module E = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Attempt
module A = Pulse.Lib.LogicalAtomicity.Atomic

(** This is a strong value comparison, not a pointer-CAS specification:
false requires old <> expected at the commitment that produces phi false. *)
let beta (#cells:N.arena) (q:Q.big_atomic cells) (expected desired old:H.value) (ok:bool) =
  Q.model q (if ok then desired else old) ** pure (ok == (old = expected))
(** Masks enumerate OPEN invariants here. The outer mask already contains
q.name, matching Iris's exclusion of the implementation namespace from the
AU's enabled mask. Client invariant opening must leave q.name open. *)
let update (#cells:N.arena) (q:Q.big_atomic cells) expected desired inner credits phi =
  A.atomic_update (Q.mask q) inner credits (Q.model q) (beta q expected desired) (fun _ ok -> phi ok)

let protocol_equiv (#cells:N.arena) (q:Q.big_atomic cells) expected desired
  : Lemma (Q.model q == P.model q.Q.core.Q.model /\
      beta q expected desired == P.beta q.Q.core.Q.model expected desired) =
  assert (Q.model q == P.model q.Q.core.Q.model) by (FStar.Tactics.V2.trefl ());
  assert (beta q expected desired == P.beta q.Q.core.Q.model expected desired)
    by (FStar.Tactics.V2.trefl ())

let unused (#cells:N.arena) expected (node:N.id cells) ok =
  if ok && expected <> N.value cells node then emp else N.ticket cells node

private fn finish (r:P.request) phi (ok:bool)
  requires loc r.P.caller ** P.tags r phi ** on r.P.caller (P.result r ok)
  ensures phi ok
{
  later_credit_buy 1;
  on_elim #r.P.caller (P.result r ok);
  P.recover_result r phi ok;
  drop_ (loc r.P.caller);
}

fn cas (#cells:N.arena) (q:Q.big_atomic cells)
  (expected:H.value) (node:N.id cells)
  (inner:inames { mem_inv inner q.Q.name }) credits phi
  preserves Q.shared q
  requires update q expected (N.value cells node) inner credits phi ** N.ticket cells node
  returns ok:bool
  ensures phi ok ** unused expected node ok
{
  // Anchor the actual AU, not just its specification. The helper can use
  // placeless model halves without acquiring the caller's local resources.
  let caller = loc_get ();
  let r = P.new_request expected (N.value cells node) caller inner credits phi;
  dup (P.tags r phi) ();
  rewrite loc caller as loc r.P.caller;
  protocol_equiv q expected (N.value cells node);
  rewrite update q expected (N.value cells node) inner credits phi
    as P.au q.Q.core.Q.model (Q.mask q) r phi;
  on_intro #r.P.caller (P.au q.Q.core.Q.model (Q.mask q) r phi);
  fold K.pre q r phi;
  slprop_equivs ();
  let sample = R.read_with q (K.pre q r phi) (K.post q r)
    (fun old -> K.backup q r phi credits old);
  let v = fst sample;
  let p = fst (snd sample);
  let ver = snd (snd sample);
  rewrite K.post q r (fst (snd sample)) as K.post q r p;
  rewrite R.sampled q (snd (snd sample)) (fst (snd sample)) (fst sample)
    as R.sampled q ver p v;
  if (v <> expected) {
    rewrite K.post q r p as (on r.P.caller (P.result r false) ** G.pts_to r.P.token ());
    drop_ (R.sampled q ver p v);
    G.free r.P.token;
    rewrite N.ticket cells node as unused expected node false;
    finish r phi false;
    false
  } else if (expected = N.value cells node) {
    rewrite K.post q r p as (on r.P.caller (P.result r true) ** G.pts_to r.P.token ());
    drop_ (R.sampled q ver p v);
    G.free r.P.token;
    rewrite N.ticket cells node as unused expected node true;
    finish r phi true;
    true
  } else {
    // A changing request is now registered. The caller has a one-shot
    // receipt; the registry owns either its AU or its completed failure.
    rewrite K.post q r p as P.registered q.Q.core.Q.pending r (Q.node_of p);
    rewrite R.sampled q ver p v as R.sampled q ver p r.P.expected;
    fold E.resources q r node ver p false;
    let ok = E.exchange q node r ver p false;
    if ok {
      rewrite E.post q r node ver p false ok
        as (on r.P.caller (P.result r true) ** V.published q ver node);
      V.try_validate q ver node;
      rewrite emp as unused expected node true;
      finish r phi true;
      true
    } else {
      rewrite E.post q r node ver p false ok
        as (N.ticket cells node ** R.sampled q ver p r.P.expected **
          P.registered q.Q.core.Q.pending r (Q.node_of p) ** E.first_failure q p);
      fold E.resources q r node ver p true;
      let ok = E.exchange q node r ver p true;
      if ok {
        rewrite E.post q r node ver p true ok
          as (on r.P.caller (P.result r true) ** V.published q ver node);
        V.try_validate q ver node;
        rewrite emp as unused expected node true;
        finish r phi true;
        true
      } else {
        // No AU is opened here. An intervening publication already ran the
        // failure callback, possibly when the current value was different.
        rewrite E.post q r node ver p true ok
          as (on r.P.caller (P.result r false) ** N.ticket cells node);
        rewrite N.ticket cells node as unused expected node false;
        finish r phi false;
        false
      }
    }
  }
}
