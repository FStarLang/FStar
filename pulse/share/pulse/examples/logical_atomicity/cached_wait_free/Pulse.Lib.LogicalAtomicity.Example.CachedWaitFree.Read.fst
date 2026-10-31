module Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Read
#lang-pulse

(**
The reference read': version, two independent cache loads, backup, version.
The AU commits at the backup load, before validation decides which copy to
return. The fallback uses THAT immutable backup, not a fresh pointer load.
Consequently no prophecy or retrospective commitment is needed.
*)

open Pulse.Lib.Pervasives
module G = Pulse.Lib.GhostReference
module MR = Pulse.Lib.MonotonicGhostRef
module H = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Model
module N = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Storage
module Q = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.State
module Atom = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Atomics
module D = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Actions
module M = Pulse.Lib.LogicalAtomicity.Masks
module A = Pulse.Lib.LogicalAtomicity.Atomic
module U = Pulse.Lib.LogicalAtomicity.Update

let beta (#cells:N.arena) (q:Q.big_atomic cells) (old result:H.value) =
  Q.model q old ** pure (result == old)
let update (#cells:N.arena) (q:Q.big_atomic cells) inner credits phi =
  A.atomic_update emp_inames inner credits (Q.model q) (beta q) (fun _ v -> phi v)
let opened (#cells:N.arena) (q:Q.big_atomic cells) inner credits phi =
  A.opened emp_inames inner (Q.model q) (update q inner credits phi) (beta q) (fun _ v -> phi v)
let closing (#cells:N.arena) (q:Q.big_atomic cells) inner credits phi v =
  A.closing emp_inames inner (Q.model q) (update q inner credits phi) (beta q) (fun _ v -> phi v) v

let observed (#cells:N.arena) (q:Q.big_atomic cells) (old:Q.history cells) (p:Q.pointer cells) =
  exists* (s:Q.history cells). Q.snapshot q s **
    pure (H.advances old s /\ p == Q.tag (H.current s) s.H.validated)
let post (#cells:N.arena) (q:Q.big_atomic cells) old phi (p:Q.pointer cells) =
  phi (N.value cells (Q.node_of p)) ** observed q old p
let resources (#cells:N.arena) (q:Q.big_atomic cells) old =
  Q.shared q ** later_credit 1 ** Q.snapshot q old

atomic fn backup_opened (#cells:N.arena) (q:Q.big_atomic cells)
  (old:erased (Q.history cells)) inner credits phi
  opens [q.Q.name]
  requires opened q inner credits phi ** resources q old
  returns p:Q.pointer cells
  ensures U.fupd inner emp_inames (post q old phi p) ** Q.shared q
{
  unfold resources;
  unfold Q.shared;
  dup_inv q.Q.name (Q.body q.Q.core);
  let p = with_invariants_a (Q.pointer cells) emp_inames q.Q.name (Q.body q.Q.core)
    (opened q inner credits phi ** Q.snapshot q old)
    (fun p -> U.fupd inner emp_inames (post q old phi p)) fn _ {
    unfold Q.body;
    with s. unfold Q.state q.Q.core s;
    unfold Q.physical q.Q.core s;
    unfold Q.snapshot;
    MR.recall_snapshot q.Q.core.Q.history;
    unfold opened;
    unfold A.opened;
    with v. _;
    unfold Q.model;
    G.pts_to_injective_eq q.Q.core.Q.model;
    let p = Atom.read q.Q.core.Q.backup;
    MR.take_snapshot q.Q.core.Q.history s;
    fold Q.snapshot q s;
    fold observed q old p;
    fold Q.model q v;
    fold beta q v (N.value cells (Q.node_of p));
    fold closing q inner credits phi v;
    fold Q.physical q.Q.core s;
    fold Q.state q.Q.core s;
    fold Q.body q.Q.core;
    D.delay inner
      ((closing q inner credits phi v ** beta q v (N.value cells (Q.node_of p))) ** observed q old p)
      (post q old phi p)
      (fun _ -> M.frame_ghost (observed q old p)
        (A.commit emp_inames inner (Q.model q) (update q inner credits phi)
          (beta q) (fun _ v -> phi v) v (N.value cells (Q.node_of p))));
    p
  };
  fold Q.shared q;
  p
}

fn backup (#cells:N.arena) (q:Q.big_atomic cells)
  (old:erased (Q.history cells))
  (inner:inames { not (mem_inv inner q.Q.name) }) credits phi
  preserves Q.shared q
  requires update q inner credits phi ** Q.snapshot q old
  returns p:Q.pointer cells
  ensures post q old phi p
{
  later_credit_buy credits;
  later_credit_buy 1;
  fold resources q old;
  unfold update;
  slprop_equivs ();
  D.with_update inner (add_inv emp_inames q.Q.name) credits (Q.model q) (beta q)
    (fun _ v -> phi v) (resources q old) (Q.shared q) (post q old phi)
    (fun _ -> backup_opened q old inner credits phi)
}

(** Retain the initial version and the backup observation for a subsequent
publication attempt. Neither snapshot asserts that the backup is current. *)
let started (#cells:N.arena) (q:Q.big_atomic cells) ver (s:Q.history cells) =
  Q.snapshot q s ** pure (s.H.version == ver)
let seen_backup (#cells:N.arena) (q:Q.big_atomic cells) p (s:Q.history cells) =
  Q.snapshot q s ** pure (p == Q.tag (H.current s) s.H.validated)
let sampled (#cells:N.arena) (q:Q.big_atomic cells) (ver:nat)
  (p:Q.pointer cells) (v:H.value) =
  exists* (start seen:Q.history cells).
    started q ver start ** seen_backup q p seen **
    pure (H.advances start seen /\ v == N.value cells (Q.node_of p))

(** Share the physical cached-read algorithm between load and CAS. The two
backup-access instantiations issue the same single load: read' commits a
read AU there, while CAS commits a mismatch/no-op or registers its AU there.
The returned sampled facts relate both copies to THAT backup observation,
not to the value that happens to be current when this function returns. *)
fn read_with (#cells:N.arena) (q:Q.big_atomic cells) pre (phi:Q.pointer cells -> slprop)
  (get_backup:(old:erased (Q.history cells) ->
    stt (Q.pointer cells) (Q.shared q ** Q.snapshot q old ** pre)
      (fun p -> Q.shared q ** phi p ** observed q old p)))
  preserves Q.shared q
  requires pre
  returns r:(H.value & (Q.pointer cells & nat))
  ensures phi (fst (snd r)) ** sampled q (snd (snd r)) (fst (snd r)) (fst r) **
    pure (fst r == N.value cells (Q.node_of (fst (snd r))))
{
  let ver = Q.first_version q;
  with start. _;
  dup (Q.snapshot q start) ();
  fold started q ver start;
  let x = Q.read_word q true start;
  with first. _;
  let y = Q.read_word q false first;
  with second. _;
  let p = get_backup second;
  unfold observed;
  with seen. _;
  Q.tag_properties (H.current seen) seen.H.validated;
  dup (Q.snapshot q seen) ();
  fold seen_backup q p seen;
  let v = if (Q.is_valid p) {
    let final_ver = Q.last_version q seen;
    with finish. _;
    let v = if (ver = final_ver) {
      H.cached_read (N.value cells) start first second seen finish;
      ((x, y) <: H.value)
    } else {
      N.value cells (Q.node_of p)
    };
    drop_ (Q.snapshot q finish);
    v
  } else {
    drop_ (Q.snapshot q seen);
    N.value cells (Q.node_of p)
  };
  fold sampled q ver p v;
  (v, (p, ver))
}

fn read' (#cells:N.arena) (q:Q.big_atomic cells)
  (inner:inames { not (mem_inv inner q.Q.name) }) credits phi
  preserves Q.shared q
  requires update q inner credits phi
  returns r:(H.value & (Q.pointer cells & nat))
  ensures phi (fst r) ** sampled q (snd (snd r)) (fst (snd r)) (fst r)
{
  fn get_backup (old:erased (Q.history cells))
    preserves Q.shared q
    requires Q.snapshot q old ** update q inner credits phi
    returns p:Q.pointer cells
    ensures phi (N.value cells (Q.node_of p)) ** observed q old p
  {
    let p = backup q old inner credits phi;
    unfold post;
    p
  };
  slprop_equivs ();
  let r = read_with q (update q inner credits phi)
    (fun p -> phi (N.value cells (Q.node_of p))) (fun old -> get_backup old);
  rewrite phi (N.value cells (Q.node_of (fst (snd r)))) as phi (fst r);
  r
}

fn read (#cells:N.arena) (q:Q.big_atomic cells)
  (inner:inames { not (mem_inv inner q.Q.name) }) credits phi
  preserves Q.shared q
  requires update q inner credits phi
  returns v:H.value
  ensures phi v
{
  let r = read' q inner credits phi;
  drop_ (sampled q (snd (snd r)) (fst (snd r)) (fst r));
  fst r
}
