module Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Validate
#lang-pulse

(**
Best-effort cache installation, AFTER the abstract update has committed.
An old writer may not acquire a newer version; an unlock does not itself
validate the backup. A concurrent publication can make the final unmark fail.
Every concrete read, exchange and word store is a separate atomic action.
*)

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module G = Pulse.Lib.GhostReference
module MR = Pulse.Lib.MonotonicGhostRef
module S = FStar.Seq
module H = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Model
module N = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Storage
module Q = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.State
module R = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Read
module Atom = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Atomics

let publication (#cells:N.arena) (q:Q.big_atomic cells) node (s:Q.history cells) =
  Q.snapshot q s ** pure (H.current s == node)
let published (#cells:N.arena) (q:Q.big_atomic cells) ver node =
  exists* (start now:Q.history cells).
    R.started q ver start ** publication q node now **
    pure (H.advances start now /\ start.H.cached + 1 < S.length now.H.nodes)

(** The writer capability includes both version and current cache contents.
After writing word one, its half agrees with the half retained in the
invariant; this protects word one while word two is still to be stored.
Merely remembering an odd version would not establish that stability. *)
let held (#cells:N.arena) (q:Q.big_atomic cells) ver node cache =
  exists* (s:Q.history cells).
    Q.snapshot q s ** G.pts_to q.Q.core.Q.writer #0.5R (ver, cache) **
    pure (s.H.version == ver /\ not (H.even ver) /\ S.index s.H.nodes s.H.target == node)

let released (#cells:N.arena) (q:Q.big_atomic cells) node =
  exists* (s:Q.history cells). Q.snapshot q s **
    pure (H.even s.H.version /\ S.index s.H.nodes s.H.cached == node)

fn try_lock (#cells:N.arena) (q:Q.big_atomic cells) (ver:nat) (node:N.id cells)
  preserves Q.shared q
  requires published q ver node
  returns ok:bool
  ensures cond ok (exists* cache. held q (ver + 1) node cache) emp
{
  if (ver % 2 = 0) {
    unfold Q.shared;
    dup_inv q.Q.name (Q.body q.Q.core);
    let ok = with_invariants bool emp_inames q.Q.name (Q.body q.Q.core)
      (published q ver node)
      (fun ok -> cond ok (exists* cache. held q (ver + 1) node cache) emp) fn _ {
      unfold Q.body;
      with s. unfold Q.state q.Q.core s;
      unfold Q.physical q.Q.core s;
      unfold published;
      with start pub. _;
      unfold R.started;
      unfold publication;
      unfold Q.snapshot q start;
      MR.recall_snapshot q.Q.core.Q.history #1.0R #s #start;
      unfold Q.snapshot q pub;
      MR.recall_snapshot q.Q.core.Q.history #1.0R #s #pub;
      let seen = Atom.exchange q.Q.core.Q.version ver (ver + 1);
      if (seen = ver) {
        let after:erased (Q.history cells) =
          hide (H.acquire (N.value cells) s (S.length pub.H.nodes - 1));
        assert pure (after.H.version == ver + 1);
        G.write q.Q.core.Q.writer (ver + 1, after.H.cache);
        Q.split_writer q (ver + 1) after.H.cache;
        MR.update q.Q.core.Q.history after;
        MR.take_snapshot q.Q.core.Q.history after;
        fold Q.snapshot q after;
        fold held q (ver + 1) node after.H.cache;
        rewrite N.used cells s.H.nodes as N.used cells after.H.nodes;
        fold Q.physical q.Q.core after;
        Q.same_nodes q.Q.core s after;
        fold Q.body q.Q.core;
        fold cond true (exists* cache. held q (ver + 1) node cache) emp;
        true
      } else {
        fold Q.physical q.Q.core s;
        fold Q.state q.Q.core s;
        fold Q.body q.Q.core;
        fold cond false (exists* cache. held q (ver + 1) node cache) emp;
        false
      }
    };
    fold Q.shared q;
    ok
  } else {
    drop_ (published q ver node);
    fold cond false (exists* cache. held q (ver + 1) node cache) emp;
    false
  }
}

fn write_word (#cells:N.arena) (q:Q.big_atomic cells) ver (node:N.id cells)
  (first:bool) (cache:erased H.value)
  preserves Q.shared q
  requires held q ver node cache
  ensures held q ver node
    (if first then (fst (N.value cells node), snd cache) else (fst cache, snd (N.value cells node)))
{
  unfold Q.shared;
  dup_inv q.Q.name (Q.body q.Q.core);
  with_invariants unit emp_inames q.Q.name (Q.body q.Q.core)
    (held q ver node cache)
    (fun _ -> held q ver node
      (if first then (fst (N.value cells node), snd cache) else (fst cache, snd (N.value cells node)))) fn _ {
    unfold Q.body;
    with s. unfold Q.state q.Q.core s;
    unfold Q.physical q.Q.core s;
    unfold held;
    with old. _;
    G.pts_to_injective_eq q.Q.core.Q.writer;
    unfold Q.snapshot;
    MR.recall_snapshot q.Q.core.Q.history;
    G.gather q.Q.core.Q.writer;
    if first {
      Atom.write q.Q.core.Q.first (fst (N.value cells node));
      let after:erased (Q.history cells) = hide (H.write_first (N.value cells) s (fst (N.value cells node)));
      G.write q.Q.core.Q.writer (ver, after.H.cache);
      Q.split_writer q ver after.H.cache;
      MR.update q.Q.core.Q.history after;
      MR.take_snapshot q.Q.core.Q.history after;
      fold Q.snapshot q after;
      fold held q ver node after.H.cache;
      rewrite N.used cells s.H.nodes as N.used cells after.H.nodes;
      fold Q.physical q.Q.core after;
      Q.same_nodes q.Q.core s after;
      rewrite held q ver node after.H.cache as held q ver node
        (if first then (fst (N.value cells node), snd cache) else (fst cache, snd (N.value cells node)));
    } else {
      Atom.write q.Q.core.Q.second (snd (N.value cells node));
      let after:erased (Q.history cells) = hide (H.write_second (N.value cells) s (snd (N.value cells node)));
      G.write q.Q.core.Q.writer (ver, after.H.cache);
      Q.split_writer q ver after.H.cache;
      MR.update q.Q.core.Q.history after;
      MR.take_snapshot q.Q.core.Q.history after;
      fold Q.snapshot q after;
      fold held q ver node after.H.cache;
      rewrite N.used cells s.H.nodes as N.used cells after.H.nodes;
      fold Q.physical q.Q.core after;
      Q.same_nodes q.Q.core s after;
      rewrite held q ver node after.H.cache as held q ver node
        (if first then (fst (N.value cells node), snd cache) else (fst cache, snd (N.value cells node)));
    };
    rewrite held q ver node
      (fst (match first with | true -> N.value cells node | false -> cache),
       snd (match first with | true -> cache | false -> N.value cells node))
      as held q ver node
        (if first then (fst (N.value cells node), snd cache) else (fst cache, snd (N.value cells node)));
    fold Q.body q.Q.core;
  };
  fold Q.shared q;
}

fn unlock (#cells:N.arena) (q:Q.big_atomic cells) ver (node:N.id cells)
  preserves Q.shared q
  requires held q ver node (N.value cells node)
  ensures released q node
{
  unfold Q.shared;
  dup_inv q.Q.name (Q.body q.Q.core);
  with_invariants unit emp_inames q.Q.name (Q.body q.Q.core)
    (held q ver node (N.value cells node)) (fun _ -> released q node) fn _ {
    unfold Q.body;
    with s. unfold Q.state q.Q.core s;
    unfold Q.physical q.Q.core s;
    unfold held;
    with old. _;
    G.pts_to_injective_eq q.Q.core.Q.writer;
    unfold Q.snapshot;
    MR.recall_snapshot q.Q.core.Q.history;
    let after:erased (Q.history cells) = hide (H.release (N.value cells) s);
    Atom.write q.Q.core.Q.version (ver + 1);
    G.gather q.Q.core.Q.writer;
    G.write q.Q.core.Q.writer (after.H.version, after.H.cache);
    MR.update q.Q.core.Q.history after;
    MR.take_snapshot q.Q.core.Q.history after;
    fold Q.snapshot q after;
    fold released q node;
    rewrite N.used cells s.H.nodes as N.used cells after.H.nodes;
    fold Q.physical q.Q.core after;
    Q.same_nodes q.Q.core s after;
    fold Q.body q.Q.core;
  };
  fold Q.shared q;
}

fn unmark (#cells:N.arena) (q:Q.big_atomic cells) (node:N.id cells)
  preserves Q.shared q
  requires released q node
{
  unfold Q.shared;
  dup_inv q.Q.name (Q.body q.Q.core);
  with_invariants unit emp_inames q.Q.name (Q.body q.Q.core)
    (released q node) (fun _ -> emp) fn _ {
    unfold Q.body;
    with s. unfold Q.state q.Q.core s;
    unfold Q.physical q.Q.core s;
    unfold released;
    with old. _;
    unfold Q.snapshot;
    MR.recall_snapshot q.Q.core.Q.history;
    let seen = Atom.exchange q.Q.core.Q.backup (Q.tag node false) (Q.tag node true);
    Q.tag_properties (H.current s) s.H.validated;
    Q.tag_properties node false;
    if (seen = Q.tag node false) {
      assert pure (H.current s == node /\ not s.H.validated);
      H.can_validate (N.value cells) old s old.H.cached;
      let after:erased (Q.history cells) = hide (H.validate (N.value cells) s);
      MR.update q.Q.core.Q.history after;
      rewrite N.used cells s.H.nodes as N.used cells after.H.nodes;
      fold Q.physical q.Q.core after;
      Q.same_nodes q.Q.core s after;
    } else {
      fold Q.physical q.Q.core s;
      fold Q.state q.Q.core s;
    };
    fold Q.body q.Q.core;
  };
  fold Q.shared q;
}

fn try_validate (#cells:N.arena) (q:Q.big_atomic cells) (ver:nat) (node:N.id cells)
  preserves Q.shared q
  requires published q ver node
{
  let ok = try_lock q ver node;
  if ok {
    elim_cond_true _ _ _;
    with cache. _;
    write_word q (ver + 1) node true cache;
    write_word q (ver + 1) node false (fst (N.value cells node), snd cache);
    rewrite held q (ver + 1) node (fst (N.value cells node), snd (N.value cells node))
      as held q (ver + 1) node (N.value cells node);
    unlock q (ver + 1) node;
    unmark q node;
  } else {
    elim_cond_false _ _ _;
  }
}
