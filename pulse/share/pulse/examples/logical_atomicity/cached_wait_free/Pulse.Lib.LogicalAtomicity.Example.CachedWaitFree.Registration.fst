module Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Registration
#lang-pulse

(**
Register at the backup load, not after the whole cached read returns.

This is the registration point inside cas_spec in the pinned Iris proof
cited in CAS.fst. A publication between reading the backup and announcing
the AU must not be missed: that publication might be the only time expected
differs from the abstract value before an A--B--A return.

At this physical load, opening the AU agrees with the invariant's current
model half. Mismatch commits false; equal expected/desired commits true as a
no-op. Otherwise abort this initial opening and put the restored AU, fresh
opening credits, and observed epoch in the registry before closing q.name.
Subsequent cache validation changes only which copy Read returns, not this
registration or the already-committed mismatch/no-op result.
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
module Atom = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Atomics
module M = Pulse.Lib.LogicalAtomicity.Masks
module U = Pulse.Lib.LogicalAtomicity.Update
module L = Pulse.Lib.LogicalAtomicity.Locality

let post (#cells:N.arena) (q:Q.big_atomic cells) (r:P.request) (p:Q.pointer cells) =
  let v = N.value cells (Q.node_of p) in
  if v <> r.P.expected then on r.P.caller (P.result r false) ** G.pts_to r.P.token ()
  else if r.P.expected = r.P.desired then on r.P.caller (P.result r true) ** G.pts_to r.P.token ()
  else P.registered q.Q.core.Q.pending r (Q.node_of p)

let pre (#cells:N.arena) (q:Q.big_atomic cells) r phi =
  on r.P.caller (P.au q.Q.core.Q.model (Q.mask q) r phi) ** P.tags r phi ** G.pts_to r.P.token ()

private ghost fn finish_result (#cells:N.arena) (q:Q.big_atomic cells) r phi
  (s:Q.history cells) (p:Q.pointer cells { p == Q.tag (H.current s) s.H.validated })
  (ok:bool { if ok then N.value cells (Q.node_of p) == r.P.expected /\ r.P.expected == r.P.desired
            else N.value cells (Q.node_of p) =!= r.P.expected })
  requires on r.P.caller (phi ok) **
    (Q.state q.Q.core s ** P.initialized q.Q.core.Q.pending q.Q.name **
      P.tags r phi ** G.pts_to r.P.token ())
  ensures Q.body q.Q.core ** post q r p
{
  P.pack_result r phi ok;
  drop_ (P.initialized q.Q.core.Q.pending q.Q.name);
  fold Q.body q.Q.core;
  rewrite (on r.P.caller (P.result r ok) ** G.pts_to r.P.token ()) as post q r p;
}

private ghost fn finish_registration (#cells:N.arena) (q:Q.big_atomic cells)
  (r:P.request) phi (s:Q.history cells)
  (p:Q.pointer cells { p == Q.tag (H.current s) s.H.validated /\
    N.value cells (Q.node_of p) == r.P.expected /\ r.P.expected =!= r.P.desired })
  requires on r.P.caller (P.au q.Q.core.Q.model (Q.mask q) r phi) **
    (Q.state q.Q.core s ** P.initialized q.Q.core.Q.pending q.Q.name **
      P.tags r phi ** later_credit r.P.credits ** G.pts_to r.P.token ())
  ensures Q.body q.Q.core ** post q r p
{
  Q.tag_properties (H.current s) s.H.validated;
  unfold Q.state;
  P.expose cells q.Q.core.Q.model q.Q.core.Q.pending s.H.nodes q.Q.name;
  with es. assert (P.content cells q.Q.core.Q.model q.Q.core.Q.pending s.H.nodes (Some q.Q.name) es);
  P.register cells q.Q.core.Q.model q.Q.core.Q.pending s.H.nodes q.Q.name es phi r;
  fold Q.state q.Q.core s;
  fold Q.body q.Q.core;
  drop_ (P.initialized q.Q.core.Q.pending q.Q.name);
  rewrite P.registered q.Q.core.Q.pending r (S.index s.H.nodes (S.length s.H.nodes - 1))
    as post q r p;
}

private ghost fn decide (#cells:N.arena) (q:Q.big_atomic cells) r phi
  (s:Q.history cells) (p:Q.pointer cells { p == Q.tag (H.current s) s.H.validated })
  requires P.opened q.Q.core.Q.model (Q.mask q) r phi **
    Q.state q.Q.core s ** P.initialized q.Q.core.Q.pending q.Q.name **
    P.tags r phi ** later_credit r.P.credits ** G.pts_to r.P.token ()
  ensures U.fupd r.P.inner (Q.mask q) (Q.body q.Q.core ** post q r p)
{
  unfold P.opened;
  unfold L.opened;
  with old. assert (P.model q.Q.core.Q.model old);
  fold P.held q.Q.core.Q.model (Q.mask q) r phi old;
  unfold Q.state;
  unfold P.model;
  G.pts_to_injective_eq q.Q.core.Q.model;
  Q.tag_properties (H.current s) s.H.validated;
  assert pure (old == N.value cells (Q.node_of p));
  fold P.model q.Q.core.Q.model old;
  fold Q.state q.Q.core s;
  slprop_equivs ();
  let expected = r.P.expected;
  let desired = r.P.desired;
  if (N.value cells (Q.node_of p) <> expected) {
    drop_ (later_credit r.P.credits);
    fold P.beta q.Q.core.Q.model r.P.expected r.P.desired old false;
    P.delay r.P.inner (Q.mask q)
      ((P.held q.Q.core.Q.model (Q.mask q) r phi old **
        P.beta q.Q.core.Q.model r.P.expected r.P.desired old false) **
        (Q.state q.Q.core s ** P.initialized q.Q.core.Q.pending q.Q.name **
          P.tags r phi ** G.pts_to r.P.token ()))
      (Q.body q.Q.core ** post q r p)
      (fun _ -> M.bind_ghost
        (M.frame_ghost (Q.state q.Q.core s ** P.initialized q.Q.core.Q.pending q.Q.name **
          P.tags r phi ** G.pts_to r.P.token ())
          (P.commit q.Q.core.Q.model (Q.mask q) r phi old false))
        (fun _ -> M.lift_ghost (Q.mask q) (finish_result q r phi s p false)));
  } else if (expected = desired) {
    drop_ (later_credit r.P.credits);
    rewrite P.model q.Q.core.Q.model old as P.model q.Q.core.Q.model r.P.desired;
    fold P.beta q.Q.core.Q.model r.P.expected r.P.desired old true;
    P.delay r.P.inner (Q.mask q)
      ((P.held q.Q.core.Q.model (Q.mask q) r phi old **
        P.beta q.Q.core.Q.model r.P.expected r.P.desired old true) **
        (Q.state q.Q.core s ** P.initialized q.Q.core.Q.pending q.Q.name **
          P.tags r phi ** G.pts_to r.P.token ()))
      (Q.body q.Q.core ** post q r p)
      (fun _ -> M.bind_ghost
        (M.frame_ghost (Q.state q.Q.core s ** P.initialized q.Q.core.Q.pending q.Q.name **
          P.tags r phi ** G.pts_to r.P.token ())
          (P.commit q.Q.core.Q.model (Q.mask q) r phi old true))
        (fun _ -> M.lift_ghost (Q.mask q) (finish_result q r phi s p true)));
  } else {
    unfold P.held;
    fold L.opened r.P.caller (Q.mask q) r.P.inner r.P.credits (P.model q.Q.core.Q.model)
      (P.beta q.Q.core.Q.model r.P.expected r.P.desired) (fun _ ok -> phi ok);
    fold P.opened q.Q.core.Q.model (Q.mask q) r phi;
    P.delay r.P.inner (Q.mask q)
      (P.opened q.Q.core.Q.model (Q.mask q) r phi **
        (Q.state q.Q.core s ** P.initialized q.Q.core.Q.pending q.Q.name **
          P.tags r phi ** later_credit r.P.credits ** G.pts_to r.P.token ()))
      (Q.body q.Q.core ** post q r p)
      (fun _ -> M.bind_ghost
        (M.frame_ghost (Q.state q.Q.core s ** P.initialized q.Q.core.Q.pending q.Q.name **
          P.tags r phi ** later_credit r.P.credits ** G.pts_to r.P.token ())
          (P.abort q.Q.core.Q.model (Q.mask q) r phi))
        (fun _ -> M.lift_ghost (Q.mask q) (finish_registration q r phi s p)));
  }
}

atomic fn backup_core (#cells:N.arena) (q:Q.big_atomic cells) r phi
  (old:erased (Q.history cells))
  preserves P.initialized q.Q.core.Q.pending q.Q.name
  requires Q.body q.Q.core ** Q.snapshot q old ** pre q r phi **
    later_credit r.P.credits ** later_credit r.P.credits
  returns p:Q.pointer cells
  ensures U.fupd (Q.mask q) (Q.mask q) (Q.body q.Q.core ** post q r p ** R.observed q old p)
{
  dup (P.initialized q.Q.core.Q.pending q.Q.name) ();
  unfold Q.body;
  with s. unfold Q.state q.Q.core s;
  unfold Q.physical;
  unfold Q.snapshot;
  MR.recall_snapshot q.Q.core.Q.history #1.0R #s #old;
  let p = Atom.read q.Q.core.Q.backup;
  Q.tag_properties (H.current s) s.H.validated;
  MR.take_snapshot q.Q.core.Q.history s;
  fold Q.snapshot q s;
  fold R.observed q old p;
  fold Q.physical q.Q.core s;
  fold Q.state q.Q.core s;
  unfold pre;
  slprop_equivs ();
  P.delay (Q.mask q) (Q.mask q)
    ((on r.P.caller (P.au q.Q.core.Q.model (Q.mask q) r phi) ** later_credit r.P.credits) **
      (Q.state q.Q.core s ** P.initialized q.Q.core.Q.pending q.Q.name **
        P.tags r phi ** later_credit r.P.credits ** G.pts_to r.P.token () ** R.observed q old p))
    (Q.body q.Q.core ** post q r p ** R.observed q old p)
    (fun _ -> M.bind_ghost
      (M.frame_ghost
        (Q.state q.Q.core s ** P.initialized q.Q.core.Q.pending q.Q.name **
          P.tags r phi ** later_credit r.P.credits ** G.pts_to r.P.token () ** R.observed q old p)
        (P.open_request q.Q.core.Q.model (Q.mask q) r phi))
      (fun _ -> M.bind_ghost
        (M.lift_ghost r.P.inner
          (frame_ghost (R.observed q old p) (decide q r phi s p)))
        (fun _ -> M.frame_ghost (R.observed q old p)
          (U.elim_update r.P.inner (Q.mask q) (Q.body q.Q.core ** post q r p)))));
  p
}

fn backup (#cells:N.arena) (q:Q.big_atomic cells) r phi
  (credits:nat { credits == r.P.credits })
  (old:erased (Q.history cells))
  preserves Q.shared q
  requires Q.snapshot q old ** pre q r phi
  returns p:Q.pointer cells
  ensures post q r p ** R.observed q old p
{
  later_credit_buy 1;
  // One budget opens the AU now. A separate budget accompanies a pending
  // request so a later helper can open it without spending its own credits.
  later_credit_buy credits;
  later_credit_buy credits;
  rewrite each credits as r.P.credits;
  slprop_equivs ();
  Q.with_body q
    (Q.snapshot q old ** pre q r phi ** later_credit r.P.credits ** later_credit r.P.credits)
    (fun p -> post q r p ** R.observed q old p)
    (fun _ -> backup_core q r phi old)
}
