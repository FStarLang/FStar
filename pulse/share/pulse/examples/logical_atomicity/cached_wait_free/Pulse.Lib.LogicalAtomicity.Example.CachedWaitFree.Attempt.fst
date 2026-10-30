module Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Attempt
#lang-pulse

(**
The two physical publication attempts of the Iris cas cited in CAS.fst.

The first compares the captured tagged pointer; the second compares that
same node's unmarked encoding. Losing once is not enough to return false:
a cache writer might only have unmarked the node, without changing its value.
After both attempts fail, two_failures proves an intervening publication,
and the registry supplies the failure already committed by that publisher.
Successful attempts perform their own commitment and failure helping as
ghost cleanup of the single successful exchange.
*)

open Pulse.Lib.Pervasives
module G = Pulse.Lib.GhostReference
module MR = Pulse.Lib.MonotonicGhostRef
module S = FStar.Seq
module H = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Model
module N = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Storage
module P = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Registry
module Q = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.State
module R = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Read
module V = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Validate
module Atom = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Atomics
module M = Pulse.Lib.LogicalAtomicity.Masks
module U = Pulse.Lib.LogicalAtomicity.Update

let failure_at (#cells:N.arena) (q:Q.big_atomic cells) p
  (observed failed:Q.history cells) =
  Q.snapshot q failed **
    pure (H.advances observed failed /\
      p == Q.tag (H.current observed) observed.H.validated /\
      Q.tag (H.current failed) failed.H.validated =!= p)
let first_failure (#cells:N.arena) (q:Q.big_atomic cells) p =
  exists* observed failed. failure_at q p observed failed

(** If the node identity had not changed, uniqueness and prefix history would
force equal publication-history lengths at all three observations. The first
failure could then only be an unmark. Model.advances makes that validation
monotone until a new publication, so the second, unmarked-pointer CAS would
succeed. Thus two failures imply a new identity, not merely a changed tag.
This deliberately says nothing about unequal VALUES: A--B--A is allowed. *)
let two_failures (#cells:N.arena) (observed failed now:Q.history cells)
  (p:Q.pointer cells)
  : Lemma
      (requires H.advances observed failed /\ H.advances failed now /\
        p == Q.tag (H.current observed) observed.H.validated /\
        Q.tag (H.current failed) failed.H.validated =!= p /\
        Q.tag (H.current now) now.H.validated =!= Q.tag (Q.node_of p) true)
      (ensures H.current now =!= Q.node_of p) =
  Q.tag_properties (H.current observed) observed.H.validated;
  if H.current now = Q.node_of p then (
    H.same_node observed now (S.length observed.H.nodes - 1) (S.length now.H.nodes - 1);
    assert (S.length observed.H.nodes == S.length now.H.nodes);
    assert (S.length failed.H.nodes == S.length now.H.nodes);
    assert (H.current failed == H.current now);
    assert (failed.H.validated);
    assert (now.H.validated)
  )

let resources (#cells:N.arena) (q:Q.big_atomic cells) r (node:N.id cells) ver p second =
  N.ticket cells node ** R.sampled q ver p r.P.expected **
  P.registered q.Q.core.Q.pending r (Q.node_of p) **
  (if second then first_failure q p else emp)

let post (#cells:N.arena) (q:Q.big_atomic cells) r (node:N.id cells) ver p second ok =
  if ok then on r.P.caller (P.result r true) ** V.published q ver node
  else if second then on r.P.caller (P.result r false) ** N.ticket cells node
  else N.ticket cells node ** R.sampled q ver p r.P.expected **
    P.registered q.Q.core.Q.pending r (Q.node_of p) ** first_failure q p

private ghost fn record_failure (#cells:N.arena) (q:Q.big_atomic cells)
  (s:Q.history cells) ver (p:Q.pointer cells {
    Q.tag (H.current s) s.H.validated =!= p }) expected
  preserves MR.pts_to q.Q.core.Q.history #1.0R s ** R.sampled q ver p expected
  ensures first_failure q p
{
  unfold R.sampled;
  with start observed. assert (R.started q ver start ** R.seen_backup q p observed);
  unfold R.seen_backup;
  dup (Q.snapshot q observed) ();
  unfold Q.snapshot q observed;
  MR.recall_snapshot q.Q.core.Q.history #1.0R #s #observed;
  MR.take_snapshot q.Q.core.Q.history s;
  fold Q.snapshot q s;
  fold failure_at q p observed s;
  fold first_failure q p;
  fold R.seen_backup q p observed;
  fold R.sampled q ver p expected;
}

private ghost fn finish_publish (#cells:N.arena) (q:Q.big_atomic cells) r
  (node:N.id cells) ver p second (after:Q.history cells { H.current after == node })
  requires (P.body cells q.Q.core.Q.model q.Q.core.Q.pending after.H.nodes **
      G.pts_to q.Q.core.Q.model #0.5R (N.value cells node) ** on r.P.caller (P.result r true)) **
    (Q.physical q.Q.core after ** V.published q ver node)
  ensures Q.body q.Q.core ** post q r node ver p second true
{
  rewrite G.pts_to q.Q.core.Q.model #0.5R (N.value cells node)
    as G.pts_to q.Q.core.Q.model #0.5R (N.value cells (H.current after));
  fold Q.state q.Q.core after;
  fold Q.body q.Q.core;
  rewrite (on r.P.caller (P.result r true) ** V.published q ver node)
    as post q r node ver p second true;
}

atomic fn exchange_core (#cells:N.arena) (q:Q.big_atomic cells)
  (node:N.id cells) (r:P.request { r.P.desired == N.value cells node /\ r.P.expected =!= r.P.desired })
  ver (p:Q.pointer cells) (second:bool)
  preserves P.initialized q.Q.core.Q.pending q.Q.name
  requires Q.body q.Q.core ** resources q r node ver p second
  returns ok:bool
  ensures U.fupd (Q.mask q) (Q.mask q) (Q.body q.Q.core ** post q r node ver p second ok)
{
  unfold resources;
  unfold Q.body;
  with s. unfold Q.state q.Q.core s;
  unfold Q.physical;
  Q.tag_properties (Q.node_of p) true;
  let compare = if second { Q.tag (Q.node_of p) true } else { (p <: nat) };
  let seen = Atom.exchange q.Q.core.Q.backup compare (Q.tag node false);
  Q.tag_properties (H.current s) s.H.validated;
  if (seen = compare) {
    if second {
      rewrite (if second then first_failure q p else emp) as first_failure q p;
      drop_ (first_failure q p);
    } else {
      rewrite (if second then first_failure q p else emp) as emp;
    };
    unfold R.sampled;
    with start observed. assert (R.started q ver start ** R.seen_backup q p observed);
    unfold R.started;
    dup (Q.snapshot q start) ();
    unfold Q.snapshot q start;
    MR.recall_snapshot q.Q.core.Q.history #1.0R #s #start;
    fold R.started q ver start;
    drop_ (R.seen_backup q p observed);
    assert pure (H.current s == Q.node_of p);
    rewrite P.registered q.Q.core.Q.pending r (Q.node_of p)
      as P.registered q.Q.core.Q.pending r (H.current s);
    N.fresh cells s.H.nodes node;
    let after:erased (Q.history cells) = hide (H.publish (N.value cells) s node);
    N.append cells s.H.nodes node;
    rewrite N.used cells (S.append s.H.nodes (S.create 1 node)) as N.used cells after.H.nodes;
    MR.update q.Q.core.Q.history after;
    MR.take_snapshot q.Q.core.Q.history after;
    fold Q.snapshot q after;
    fold V.publication q node after;
    fold V.published q ver node;
    fold Q.physical q.Q.core after;
    // Keep the changed physical state framed while the winner and losers
    // run their ghost callbacks. Q.body is restored only after all helpers.
    P.publish cells q.Q.core.Q.model q.Q.core.Q.pending s.H.nodes node q.Q.name r;
    rewrite each (S.append s.H.nodes (S.create 1 node)) as after.H.nodes;
    slprop_equivs ();
    P.delay (Q.mask q) (Q.mask q)
      (U.fupd (Q.mask q) (Q.mask q)
        (P.body cells q.Q.core.Q.model q.Q.core.Q.pending after.H.nodes **
          G.pts_to q.Q.core.Q.model #0.5R (N.value cells node) ** on r.P.caller (P.result r true)) **
        (Q.physical q.Q.core after ** V.published q ver node))
      (Q.body q.Q.core ** post q r node ver p second true)
      (fun _ -> M.bind_ghost
        (M.frame_ghost (Q.physical q.Q.core after ** V.published q ver node)
          (U.elim_update (Q.mask q) (Q.mask q)
            (P.body cells q.Q.core.Q.model q.Q.core.Q.pending after.H.nodes **
              G.pts_to q.Q.core.Q.model #0.5R (N.value cells node) ** on r.P.caller (P.result r true))))
        (fun _ -> M.lift_ghost (Q.mask q) (finish_publish q r node ver p second after)));
    true
  } else if second {
    rewrite (if second then first_failure q p else emp) as first_failure q p;
    unfold first_failure;
    with observed failed. unfold failure_at q p observed failed;
    unfold Q.snapshot;
    MR.recall_snapshot q.Q.core.Q.history #1.0R #s #failed;
    two_failures observed failed s p;
    drop_ (R.sampled q ver p r.P.expected);
    P.expose cells q.Q.core.Q.model q.Q.core.Q.pending s.H.nodes q.Q.name;
    with es. assert (P.content cells q.Q.core.Q.model q.Q.core.Q.pending s.H.nodes (Some q.Q.name) es);
    P.take_result cells q.Q.core.Q.model q.Q.core.Q.pending s.H.nodes q.Q.name es r (Q.node_of p);
    fold Q.physical q.Q.core s;
    fold Q.state q.Q.core s;
    fold Q.body q.Q.core;
    rewrite (on r.P.caller (P.result r false) ** N.ticket cells node)
      as post q r node ver p second false;
    U.return_update (Q.mask q) (Q.body q.Q.core ** post q r node ver p second false);
    false
  } else {
    rewrite (if second then first_failure q p else emp) as emp;
    record_failure q s ver p r.P.expected;
    fold Q.physical q.Q.core s;
    fold Q.state q.Q.core s;
    fold Q.body q.Q.core;
    rewrite (N.ticket cells node ** R.sampled q ver p r.P.expected **
      P.registered q.Q.core.Q.pending r (Q.node_of p) ** first_failure q p)
      as post q r node ver p second false;
    U.return_update (Q.mask q) (Q.body q.Q.core ** post q r node ver p second false);
    false
  }
}

fn exchange (#cells:N.arena) (q:Q.big_atomic cells)
  (node:N.id cells) (r:P.request { r.P.desired == N.value cells node /\ r.P.expected =!= r.P.desired })
  ver (p:Q.pointer cells) second
  preserves Q.shared q
  requires resources q r node ver p second
  returns ok:bool
  ensures post q r node ver p second ok
{
  later_credit_buy 1;
  slprop_equivs ();
  Q.with_body q (resources q r node ver p second) (post q r node ver p second)
    (fun _ -> exchange_core q node r ver p second)
}
