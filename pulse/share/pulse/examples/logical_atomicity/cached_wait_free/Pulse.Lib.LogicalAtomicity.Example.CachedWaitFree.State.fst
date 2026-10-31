module Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.State
#lang-pulse

(**
The representation invariant separates the current immutable backup from
the independently read/written cache words. History snapshots justify stale
reads; ghost halves connect the abstract value to a client's atomic update.
An odd version lends half a writer token to exactly one cache writer.

The invariant also owns Registry.body: pending AUs and saved results are
anchored to their callers, so the shared representation remains sendable
without requiring those clients' captured state to be sendable. The split
into physical, abstract model half, and registry lets one physical
publication frame its new fields while ghost helping updates the other
components. All three must agree again before the invariant is closed.
*)

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module G = Pulse.Lib.GhostReference
module MR = Pulse.Lib.MonotonicGhostRef
module U32 = FStar.UInt32
module S = FStar.Seq
module H = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Model
module N = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Storage
module Atom = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Atomics
module P = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Registry
module M = Pulse.Lib.LogicalAtomicity.Masks
module I = Pulse.Lib.LogicalAtomicity.Invariant
module U = Pulse.Lib.LogicalAtomicity.Update

type history (cells:N.arena) = s:H.state (N.id cells) { H.valid (N.value cells) s }
let tag (node:nat) (validated:bool) : nat = 2 * node + (if validated then 0 else 1)
let node_of (p:nat) : nat = p / 2
let is_valid (p:nat) : bool = p % 2 = 0
let tag_properties (n:nat) (b:bool)
  : Lemma (node_of (tag n b) == n /\ is_valid (tag n b) == b) =
  if b then () else ()
type pointer (cells:N.arena) = p:nat { node_of p < FStar.List.Tot.length cells }

noeq type core (cells:N.arena) = {
  version:B.box nat;
  backup:B.box nat;
  first:B.box U32.t;
  second:B.box U32.t;
  history:MR.mref (H.advances #(N.id cells));
  model:G.ref H.value;
  writer:G.ref (nat & H.value);
  pending:P.registry;
}

let physical (#cells:N.arena) (c:core cells) (s:history cells) =
  B.pts_to c.version s.H.version **
  B.pts_to c.backup (tag (H.current s) s.H.validated) **
  B.pts_to c.first (fst s.H.cache) ** B.pts_to c.second (snd s.H.cache) **
  MR.pts_to c.history #1.0R s **
  G.pts_to c.writer #(if H.even s.H.version then 1.0R else 0.5R) (s.H.version, s.H.cache) **
  N.used cells s.H.nodes
let state (#cells:N.arena) (c:core cells) (s:history cells) =
  physical c s ** G.pts_to c.model #0.5R (N.value cells (H.current s)) **
  P.body cells c.model c.pending s.H.nodes

let body (#cells:N.arena) (c:core cells) = exists* (s:history cells). state c s
noeq type big_atomic (cells:N.arena) = { core:core cells; name:iname }
let shared (#cells:N.arena) (q:big_atomic cells) =
  inv q.name (body q.core) ** P.initialized q.core.pending q.name
let model (#cells:N.arena) (q:big_atomic cells) (v:H.value) = G.pts_to q.core.model #0.5R v
(** CAS accesses client AUs while this implementation invariant is open.
The opposite mask polarity in Iris expresses this as excluding its name. *)
let mask (#cells:N.arena) (q:big_atomic cells) = add_inv emp_inames q.name

ghost fn same_nodes (#cells:N.arena) (c:core cells) (old:history cells)
  (after:history cells { after.H.nodes == old.H.nodes })
  requires physical c after ** G.pts_to c.model #0.5R (N.value cells (H.current old)) **
    P.body cells c.model c.pending old.H.nodes
  ensures state c after
{
  rewrite G.pts_to c.model #0.5R (N.value cells (H.current old))
    as G.pts_to c.model #0.5R (N.value cells (H.current after));
  rewrite each old.H.nodes as after.H.nodes;
  fold state c after;
}

ghost fn change_model (#cells:N.arena) (q:big_atomic cells) (old desired:H.value)
  requires model q old ** G.pts_to q.core.model #0.5R old
  ensures model q desired ** G.pts_to q.core.model #0.5R desired
{
  unfold model;
  G.gather q.core.model;
  G.write q.core.model desired;
  G.share q.core.model;
  rewrite each (1.0R /. 2.0R) as 0.5R;
  fold model q desired;
}

(** Keep fractional normalization out of the history/sequence proof contexts. *)
ghost fn split_writer (#cells:N.arena) (q:big_atomic cells) (ver:nat) (cache:H.value)
  requires G.pts_to q.core.writer (ver, cache)
  ensures G.pts_to q.core.writer #0.5R (ver, cache) **
    G.pts_to q.core.writer #0.5R (ver, cache)
{
  G.share q.core.writer;
  rewrite each (1.0R /. 2.0R) as 0.5R;
}

instance send_state (#cells:N.arena) c s : is_send (state #cells c s) =
  FStar.Tactics.Typeclasses.solve
instance send_shared (#cells:N.arena) q : is_send (shared #cells q) =
  FStar.Tactics.Typeclasses.solve

fn create (cells:N.arena) (initial:N.id cells)
  requires N.ticket cells initial
  returns q:big_atomic cells
  ensures shared q ** model q (N.value cells initial)
{
  let v = N.value cells initial;
  let version = B.alloc #nat 0;
  let backup = B.alloc (tag initial true);
  let first = B.alloc (fst v);
  let second = B.alloc (snd v);
  let history = MR.alloc #(H.state (N.id cells)) #H.advances (H.initial (N.value cells) initial);
  let g = G.alloc v;
  G.share g;
  let writer = G.alloc #(nat & H.value) (0, v);
  let pending = P.create cells g (H.initial (N.value cells) initial).H.nodes;
  N.singleton cells initial;
  let c = { version; backup; first; second; history; model=g; writer; pending };
  rewrite each version as c.version;
  rewrite each backup as c.backup;
  rewrite each first as c.first;
  rewrite each second as c.second;
  rewrite each history as c.history;
  rewrite each g as c.model;
  rewrite each writer as c.writer;
  rewrite each pending as c.pending;
  fold physical c (H.initial (N.value cells) initial);
  fold state c (H.initial (N.value cells) initial);
  fold body c;
  let name = new_invariant (body c);
  dup_inv name (body c);
  later_credit_buy 1;
  with_invariants_g unit emp_inames name (body c) (P.uninitialized c.pending)
    (fun _ -> P.initialized c.pending name) fn _ {
    unfold body;
    with s. unfold state c s;
    P.initialize cells c.model c.pending s.H.nodes name;
    fold state c s;
    fold body c;
  };
  let q = { core=c; name };
  rewrite each c as q.core;
  rewrite each name as q.name;
  rewrite each v as N.value cells initial;
  fold shared q;
  fold model q (N.value cells initial);
  q
}

let snapshot (#cells:N.arena) (q:big_atomic cells) (s:history cells) =
  MR.snapshot q.core.history s

fn first_version (#cells:N.arena) (q:big_atomic cells)
  preserves shared q
  returns ver:nat
  ensures exists* (s:history cells). snapshot q s ** pure (ver == s.H.version)
{
  unfold shared;
  dup_inv q.name (body q.core);
  let ver = with_invariants nat emp_inames q.name (body q.core) emp
    (fun ver -> exists* (s:history cells). snapshot q s ** pure (ver == s.H.version)) fn _ {
    unfold body;
    with s. unfold state q.core s;
    unfold physical q.core s;
    let ver = Atom.read q.core.version;
    MR.take_snapshot q.core.history s;
    fold snapshot q s;
    fold physical q.core s;
    fold state q.core s;
    fold body q.core;
    ver
  };
  fold shared q;
  ver
}

fn read_word (#cells:N.arena) (q:big_atomic cells) (first:bool) (old:erased (history cells))
  preserves shared q
  requires snapshot q old
  returns v:U32.t
  ensures exists* (s:history cells). snapshot q s **
    pure (H.advances old s /\ v == (if first then fst s.H.cache else snd s.H.cache))
{
  unfold shared;
  dup_inv q.name (body q.core);
  let v = with_invariants U32.t emp_inames q.name (body q.core) (snapshot q old)
    (fun v -> exists* (s:history cells). snapshot q s **
      pure (H.advances old s /\ v == (if first then fst s.H.cache else snd s.H.cache))) fn _ {
    unfold body;
    with s. unfold state q.core s;
    unfold physical q.core s;
    unfold snapshot;
    MR.recall_snapshot q.core.history;
    let v = if first { Atom.read q.core.first } else { Atom.read q.core.second };
    MR.take_snapshot q.core.history s;
    fold snapshot q s;
    fold physical q.core s;
    fold state q.core s;
    fold body q.core;
    v
  };
  fold shared q;
  v
}

fn last_version (#cells:N.arena) (q:big_atomic cells) (old:erased (history cells))
  preserves shared q
  requires snapshot q old
  returns ver:nat
  ensures exists* (s:history cells). snapshot q s ** pure (H.advances old s /\ ver == s.H.version)
{
  unfold shared;
  dup_inv q.name (body q.core);
  let ver = with_invariants nat emp_inames q.name (body q.core) (snapshot q old)
    (fun ver -> exists* (s:history cells). snapshot q s ** pure (H.advances old s /\ ver == s.H.version)) fn _ {
    unfold body;
    with s. unfold state q.core s;
    unfold physical q.core s;
    unfold snapshot;
    MR.recall_snapshot q.core.history;
    let ver = Atom.read q.core.version;
    MR.take_snapshot q.core.history s;
    fold snapshot q s;
    fold physical q.core s;
    fold state q.core s;
    fold body q.core;
    ver
  };
  fold shared q;
  ver
}

(** Keep the implementation invariant open while ghost AUs are sequenced.
Only step may perform an observable action. Its delayed cleanup must restore
the complete body, including the request registry, before this runner closes. *)
let with_body (#cells:N.arena) (#a:Type0) (q:big_atomic cells)
  (pre:slprop) (post:a -> slprop)
  (step:unit -> stt_atomic a #PulseCore.Observability.Observable emp_inames
    (body q.core ** P.initialized q.core.pending q.name ** pre)
    (fun x -> U.fupd (mask q) (mask q) (body q.core ** post x) **
      P.initialized q.core.pending q.name))
  : stt_atomic a #PulseCore.Observability.Observable all_inames (shared q ** later_credit 1 ** pre)
      (fun x -> shared q ** post x) =
  slprop_equivs ();
  M.run_closed (
    M.bind
      (M.ghost_to_action (M.sub_ghost
        (shared q ** later_credit 1 ** pre)
        (fun _ -> (body q.core ** P.initialized q.core.pending q.name ** pre) **
          inv q.name (body q.core))
        (M.frame_ghost (P.initialized q.core.pending q.name ** pre)
          (I.open_inv emp_inames q.name (body q.core)))))
      (fun _ -> M.bind
        (M.frame (inv q.name (body q.core)) (M.lift_atomic (mask q) (step ())))
        (fun x -> M.finish_ghost x (fun x -> shared q ** post x)
          (M.bind_ghost
            (M.sub_ghost
              ((U.fupd (mask q) (mask q) (body q.core ** post x) **
                P.initialized q.core.pending q.name) ** inv q.name (body q.core))
              (fun _ -> (inv q.name (body q.core) ** body q.core) **
                (P.initialized q.core.pending q.name ** post x))
              (M.frame_ghost
                (P.initialized q.core.pending q.name ** inv q.name (body q.core))
                (U.elim_update (mask q) (mask q) (body q.core ** post x))))
            (fun _ -> M.sub_ghost
              ((inv q.name (body q.core) ** body q.core) **
                (P.initialized q.core.pending q.name ** post x))
              (fun _ -> shared q ** post x)
              (M.frame_ghost (P.initialized q.core.pending q.name ** post x)
                (I.close_inv emp_inames q.name (body q.core))))))))
