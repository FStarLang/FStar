module Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Concurrent
#lang-pulse

(**
The POPL 2011 producer/consumer client, using invariant-backed atomic updates.

The producer inserts successive keys exactly once. The consumer may choose
any key; after one successful removal, a second removal of that key MUST
fail, even if the producer runs between the calls. This is a verified client
theorem, not an assertion left to the runtime harness.

The client invariant relates the set model to a producer cursor and a set of
removed keys. Each thread keeps half of its own ghost reference. Commit
callbacks combine those halves, update the client protocol, and restore the
invariant. AUs are constructed locally, rather than assumed sendable.

The tombstone set strengthens the paper's last-removed-key invariant and
supports a final-emptiness theorem after a finite producer/consumer run.
All statements are partial correctness: a consumer waiting for an insertion
may diverge without suitable scheduling/progress.
*)

open Pulse.Lib.Pervasives
module S = FStar.Seq
module G = Pulse.Lib.GhostReference
module B = Pulse.Lib.Box
module H = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Model
module P = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Protocol
module Q = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.State
module O = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Operations
module T = Pulse.Lib.LogicalAtomicity.Triple
module Task = Pulse.Lib.Task

(** Private halves authorize one producer and one consumer. *)
let producer (g:G.ref nat) (p:nat) = G.pts_to g #0.5R p
let consumer (g:G.ref (S.seq bool)) (d:S.seq bool) = G.pts_to g #0.5R d

(** Exact client protocol; neither operation implementation can inspect it. *)
let residual (q:Q.set) (gp:G.ref nat) (gc:G.ref (S.seq bool)) (s:Q.contents q.Q.cells) =
  exists* (p:nat) (d:Q.contents q.Q.cells).
    producer gp p ** consumer gc d ** pure (P.consistent s p d)

let shared (q:Q.set) (i:iname) gp gc =
  Q.is_set q ** inv i (T.payload (O.alpha q) (residual q gp gc))
instance send_shared q i gp gc : is_send (shared q i gp gc) = FStar.Tactics.Typeclasses.solve
instance dup_shared q i gp gc : duplicable (shared q i gp gc) = FStar.Tactics.Typeclasses.solve

(** Ghost-only client handle; only q survives extraction. *)
noeq type client = { set:Q.set; name:iname; produced:G.ref nat; removed:G.ref (S.seq bool) }
let valid (c:client) = shared c.set c.name c.produced c.removed
let well_named (c:client) = c.name =!= c.set.Q.name
instance send_valid c : is_send (valid c) = FStar.Tactics.Typeclasses.solve
instance dup_valid c : duplicable (valid c) = FStar.Tactics.Typeclasses.solve

(** Start the exact-partition protocol at an empty set. *)
fn create (n:nat)
  returns c:client
  ensures pure (Q.capacity c.set == n /\ well_named c) ** valid c **
    producer c.produced 0 ** consumer c.removed (P.prefix n 0)
{
  let q = Q.create n;
  let gp = G.alloc #nat 0;
  let gc = G.alloc #(S.seq bool) (P.prefix n 0);
  G.share gp;
  G.share gc;
  P.initial n;
  fold producer gp 0;
  fold consumer gc (P.prefix n 0);
  fold producer gp 0;
  fold consumer gc (P.prefix n 0);
  fold residual q gp gc (H.empty n);
  fold O.alpha q (H.empty n);
  fold T.payload (O.alpha q) (residual q gp gc);
  let i = fresh_invariant (add_inv emp_inames q.Q.name)
    (T.payload (O.alpha q) (residual q gp gc));
  fold shared q i gp gc;
  let c = { set=q; name=i; produced=gp; removed=gc };
  rewrite each q as c.set;
  rewrite each i as c.name;
  rewrite each gp as c.produced;
  rewrite each gc as c.removed;
  fold valid c;
  c
}

let produced_post c k (r:bool) = producer c.produced k ** pure r

(** Supply client ghost code at commitment. The implementation sees only AU
alpha/beta, while this callback proves freshness from the producer cursor. *)
ghost fn prepare_add (c:client) (k:Q.key c.set)
  preserves valid c
  requires producer c.produced (k - 1)
  ensures O.update c.set H.Add k (add_inv emp_inames c.name) 1 (produced_post c k)
{
  unfold valid;
  unfold shared;
  dup_inv c.name (T.payload (O.alpha c.set) (residual c.set c.produced c.removed));
  ghost fn finish (s:Q.contents c.set.Q.cells) (r:bool) ()
    requires producer c.produced (k - 1) ** residual c.set c.produced c.removed s **
      O.beta c.set H.Add k s r
    ensures T.payload (O.alpha c.set) (residual c.set c.produced c.removed) **
      produced_post c k r
  {
    unfold residual;
    with p d. _;
    unfold producer c.produced (k - 1);
    unfold producer c.produced p;
    G.pts_to_injective_eq c.produced;
    P.produce s p d;
    unfold O.beta;
    G.gather c.produced;
    G.write c.produced k;
    G.share c.produced;
    rewrite each (1.0R /. 2.0R) as 0.5R;
    fold producer c.produced k;
    fold producer c.produced k;
    fold residual c.set c.produced c.removed (H.after H.Add s k);
    fold O.alpha c.set (H.after H.Add s k);
    fold T.payload (O.alpha c.set) (residual c.set c.produced c.removed);
    fold produced_post c k r;
  };
  T.from_invariant emp_inames c.name (O.alpha c.set)
    (residual c.set c.produced c.removed) (O.beta c.set H.Add k)
    (fun _ r -> produced_post c k r) (producer c.produced (k - 1)) finish;
  fold O.update c.set H.Add k (add_inv emp_inames c.name) 1 (produced_post c k);
  fold shared c.set c.name c.produced c.removed;
  fold valid c;
}

divergent fn produce (c:client { well_named c }) (k:Q.key c.set)
  preserves valid c
  requires producer c.produced (k - 1)
  returns r:bool
  ensures producer c.produced k ** pure r
{
  prepare_add c k;
  unfold valid;
  unfold shared;
  let r = O.add c.set k (add_inv emp_inames c.name) 1 (produced_post c k);
  unfold produced_post;
  fold shared c.set c.name c.produced c.removed;
  fold valid c;
  r
}

let consumed_post (c:client) (k:Q.key c.set) (d:Q.contents c.set.Q.cells) (r:bool) =
  consumer c.removed (P.removed d k r) **
  pure (r ==> H.member (P.removed d k r) k)

(** Failed removals preserve the tombstone set; success adds exactly k. *)
ghost fn prepare_remove (c:client) (k:Q.key c.set) (d:Q.contents c.set.Q.cells)
  preserves valid c
  requires consumer c.removed d
  ensures O.update c.set H.Remove k (add_inv emp_inames c.name) 1 (consumed_post c k d)
{
  unfold valid;
  unfold shared;
  dup_inv c.name (T.payload (O.alpha c.set) (residual c.set c.produced c.removed));
  ghost fn finish (s:Q.contents c.set.Q.cells) (r:bool) ()
    requires consumer c.removed d ** residual c.set c.produced c.removed s **
      O.beta c.set H.Remove k s r
    ensures T.payload (O.alpha c.set) (residual c.set c.produced c.removed) **
      consumed_post c k d r
  {
    unfold residual;
    with p old. _;
    unfold consumer c.removed d;
    unfold consumer c.removed old;
    G.pts_to_injective_eq c.removed;
    rewrite each old as d;
    unfold O.beta;
    P.consume s p d k;
    G.gather c.removed;
    G.write c.removed (P.removed d k r);
    G.share c.removed;
    rewrite each (1.0R /. 2.0R) as 0.5R;
    fold consumer c.removed (P.removed d k r);
    fold consumer c.removed (P.removed d k r);
    fold residual c.set c.produced c.removed (H.after H.Remove s k);
    fold O.alpha c.set (H.after H.Remove s k);
    fold T.payload (O.alpha c.set) (residual c.set c.produced c.removed);
    fold consumed_post c k d r;
  };
  T.from_invariant emp_inames c.name (O.alpha c.set)
    (residual c.set c.produced c.removed) (O.beta c.set H.Remove k)
    (fun _ r -> consumed_post c k d r) (consumer c.removed d) finish;
  fold O.update c.set H.Remove k (add_inv emp_inames c.name) 1 (consumed_post c k d);
  fold shared c.set c.name c.produced c.removed;
  fold valid c;
}

divergent fn try_remove (c:client { well_named c }) (k:Q.key c.set)
  (#d:erased (Q.contents c.set.Q.cells))
  preserves valid c
  requires consumer c.removed d
  returns r:bool
  ensures consumed_post c k d r
{
  prepare_remove c k d;
  unfold valid;
  unfold shared;
  let r = O.remove c.set k (add_inv emp_inames c.name) 1 (consumed_post c k d);
  fold shared c.set c.name c.produced c.removed;
  fold valid c;
  r
}

let absent_post c d (r:bool) = consumer c.removed d ** pure (not r)

(** One constructor proves both a second removal and a membership query false.
It uses a tombstone, not an invalid assumption that interference has stopped. *)
ghost fn prepare_absent (c:client) (op:H.operation { op == H.Remove \/ op == H.Contains })
  (k:Q.key c.set) (d:Q.contents c.set.Q.cells { H.member d k })
  preserves valid c
  requires consumer c.removed d
  ensures O.update c.set op k (add_inv emp_inames c.name) 1 (absent_post c d)
{
  unfold valid;
  unfold shared;
  dup_inv c.name (T.payload (O.alpha c.set) (residual c.set c.produced c.removed));
  ghost fn finish (s:Q.contents c.set.Q.cells) (r:bool) ()
    requires consumer c.removed d ** residual c.set c.produced c.removed s **
      O.beta c.set op k s r
    ensures T.payload (O.alpha c.set) (residual c.set c.produced c.removed) **
      absent_post c d r
  {
    unfold residual;
    with p old. _;
    unfold consumer c.removed d;
    unfold consumer c.removed old;
    G.pts_to_injective_eq c.removed;
    rewrite each old as d;
    P.cannot_remove_twice s p d k;
    H.change_same s k;
    unfold O.beta;
    assert pure (not r /\ H.after op s k == s);
    rewrite Q.model c.set (H.after op s k) as Q.model c.set s;
    fold consumer c.removed d;
    fold consumer c.removed d;
    fold residual c.set c.produced c.removed s;
    fold O.alpha c.set s;
    fold T.payload (O.alpha c.set) (residual c.set c.produced c.removed);
    fold absent_post c d r;
  };
  T.from_invariant emp_inames c.name (O.alpha c.set)
    (residual c.set c.produced c.removed) (O.beta c.set op k)
    (fun _ r -> absent_post c d r) (consumer c.removed d) finish;
  fold O.update c.set op k (add_inv emp_inames c.name) 1 (absent_post c d);
  fold shared c.set c.name c.produced c.removed;
  fold valid c;
}

(** The paper's crucial assertion is exposed as an exact public postcondition. *)
divergent fn remove_again (c:client { well_named c }) (k:Q.key c.set)
  (#d:erased (Q.contents c.set.Q.cells) { H.member d k })
  preserves valid c ** consumer c.removed d
  returns r:bool
  ensures pure (not r)
{
  prepare_absent c H.Remove k d;
  unfold valid;
  unfold shared;
  let r = O.remove c.set k (add_inv emp_inames c.name) 1 (absent_post c d);
  unfold absent_post;
  fold shared c.set c.name c.produced c.removed;
  fold valid c;
  r
}

(** Match the paper's conditional second removal for an arbitrary chosen key.
If the first attempt fails, the second attempt is skipped and false returned. *)
divergent fn consume_twice (c:client { well_named c }) (k:Q.key c.set)
  (#d:erased (Q.contents c.set.Q.cells))
  preserves valid c
  requires consumer c.removed d
  returns second:bool
  ensures pure (not second) ** (exists* (d':Q.contents c.set.Q.cells). consumer c.removed d')
{
  let first = try_remove c k;
  unfold consumed_post;
  if first {
    let second = remove_again c k;
    assert pure (not second);
    second
  } else {
    false
  }
}

(** Wait until k is removed, then prove that an immediately subsequent remove
fails. The producer may run between ANY of the attempts. No fairness is assumed. *)
divergent fn rec consume_wait (c:client { well_named c }) (k:Q.key c.set)
  (#d:erased (Q.contents c.set.Q.cells))
  preserves valid c
  requires consumer c.removed d
  returns second:bool
  ensures consumer c.removed (H.change d k true) ** pure (not second)
{
  let first = try_remove c k;
  unfold consumed_post;
  if first {
    rewrite consumer c.removed (P.removed d k first)
      as consumer c.removed (H.change d k true);
    remove_again c k
  } else {
    rewrite consumer c.removed (P.removed d k first) as consumer c.removed d;
    consume_wait c k
  }
}

(** A finite prefix producer. Every add is proved to report a fresh insertion. *)
divergent fn rec produce_range (c:client { well_named c })
  (lo:Q.key c.set) (hi:Q.key c.set { lo <= hi })
  preserves valid c
  requires producer c.produced (lo - 1)
  returns all_new:bool
  ensures producer c.produced hi ** pure all_new
{
  let first = produce c lo;
  if (lo < hi) {
    rewrite producer c.produced lo as producer c.produced (lo + 1 - 1);
    let rest = produce_range c (lo + 1) hi;
    first && rest
  } else {
    rewrite producer c.produced lo as producer c.produced hi;
    first
  }
}

(** Consume a prefix and check a second removal at every key. The returned
violation flag is proved false, and the full removed-set model is retained. *)
divergent fn rec consume_range (c:client { well_named c })
  (lo:Q.key c.set) (hi:Q.key c.set { lo <= hi })
  preserves valid c
  requires consumer c.removed (P.prefix (Q.capacity c.set) (lo - 1))
  returns violation:bool
  ensures consumer c.removed (P.prefix (Q.capacity c.set) hi) ** pure (not violation)
{
  let second = consume_wait c lo;
  P.prefix_step (Q.capacity c.set) lo;
  rewrite consumer c.removed (H.change (P.prefix (Q.capacity c.set) (lo - 1)) lo true)
    as consumer c.removed (P.prefix (Q.capacity c.set) lo);
  if (lo < hi) {
    rewrite consumer c.removed (P.prefix (Q.capacity c.set) lo)
      as consumer c.removed (P.prefix (Q.capacity c.set) (lo + 1 - 1));
    let rest = consume_range c (lo + 1) hi;
    second || rest
  } else {
    rewrite consumer c.removed (P.prefix (Q.capacity c.set) lo)
      as consumer c.removed (P.prefix (Q.capacity c.set) hi);
    second
  }
}

(** Completion certificates. The exact partition in residual, together with
all keys removed, forces the model to be empty whenever the invariant opens. *)
let finished (c:client) =
  valid c ** producer c.produced (Q.capacity c.set) **
  consumer c.removed (P.prefix (Q.capacity c.set) (Q.capacity c.set))

(** Explicit final-emptiness theorem, applicable to the ACTUAL borrowed model.
This does not pretend to extract ownership from a permanent invariant. *)
ghost fn empty_at_open (c:client) (s:Q.contents c.set.Q.cells)
  preserves O.alpha c.set s ** residual c.set c.produced c.removed s **
    consumer c.removed (P.prefix (Q.capacity c.set) (Q.capacity c.set))
  ensures pure (s == H.empty (Q.capacity c.set))
{
  unfold residual;
  with p d. _;
  unfold consumer c.removed d;
  unfold consumer c.removed (P.prefix (Q.capacity c.set) (Q.capacity c.set));
  G.pts_to_injective_eq c.removed;
  rewrite each d as (P.prefix (Q.capacity c.set) (Q.capacity c.set));
  P.drained s p;
  fold consumer c.removed (P.prefix (Q.capacity c.set) (Q.capacity c.set));
  fold consumer c.removed (P.prefix (Q.capacity c.set) (Q.capacity c.set));
  fold residual c.set c.produced c.removed s;
}

(** Open the actual client invariant after joining, and apply the theorem. *)
fn certify_empty (c:client)
  preserves finished c
{
  unfold finished;
  unfold valid;
  unfold shared;
  later_credit_buy 1;
  dup_inv c.name (T.payload (O.alpha c.set) (residual c.set c.produced c.removed));
  with_invariants_g unit emp_inames c.name
    (T.payload (O.alpha c.set) (residual c.set c.produced c.removed))
    (consumer c.removed (P.prefix (Q.capacity c.set) (Q.capacity c.set)))
    (fun _ -> consumer c.removed (P.prefix (Q.capacity c.set) (Q.capacity c.set))) fn _ {
    unfold T.payload;
    with s. _;
    empty_at_open c s;
    assert pure (s == H.empty (Q.capacity c.set));
    fold T.payload (O.alpha c.set) (residual c.set c.produced c.removed);
  };
  fold shared c.set c.name c.produced c.removed;
  fold valid c;
  fold finished c;
}

(** Executable read-only client: all completed keys remain absent. *)
divergent fn contains_removed (c:client { well_named c }) (k:Q.key c.set)
  (#d:erased (Q.contents c.set.Q.cells) { H.member d k })
  preserves valid c ** consumer c.removed d
  returns r:bool
  ensures pure (not r)
{
  prepare_absent c H.Contains k d;
  unfold valid;
  unfold shared;
  let r = O.contains c.set k (add_inv emp_inames c.name) 1 (absent_post c d);
  unfold absent_post;
  fold shared c.set c.name c.produced c.removed;
  fold valid c;
  r
}

(** Check every key after completion; the returned boolean is proved true. *)
divergent fn rec check_empty_from (c:client { well_named c })
  (k:nat { 0 < k /\ k <= Q.capacity c.set + 1 })
  preserves finished c
  returns ok:bool
  ensures pure ok
{
  if (k <= Q.capacity c.set) {
    unfold finished;
    P.prefix_member (Q.capacity c.set) (Q.capacity c.set) k;
    let present = contains_removed c k;
    fold finished c;
    let rest = check_empty_from c (k + 1);
    not present && rest
  } else {
    true
  }
}

(** Spawn the actual producer and consumer, join both, and retain their precise
completion certificates. Reuse a caller-owned pool across native regressions. *)
divergent fn run_in_pool (pool:Task.pool) (n:pos)
  preserves Task.pool_alive pool
  returns result:(client & bool)
  ensures pure (Q.capacity (fst result).set == n /\ well_named (fst result) /\ not (snd result)) **
    finished (fst result)
{
  let c = create n;
  let produced_ok = B.alloc false;
  let consumed_bad = B.alloc true;
  dup (valid c) ();
  let prod = Task.spawn pool #_
    #(valid c ** producer c.produced 0 ** B.pts_to produced_ok false)
    #(valid c ** producer c.produced n ** B.pts_to produced_ok true)
    fn _ {
      let ok = produce_range c 1 n;
      B.(produced_ok := ok);
    };
  dup (valid c) ();
  let cons = Task.spawn pool #_
    #(valid c ** consumer c.removed (P.prefix n 0) ** B.pts_to consumed_bad true)
    #(valid c ** consumer c.removed (P.prefix n n) ** B.pts_to consumed_bad false)
    fn _ {
      rewrite consumer c.removed (P.prefix n 0)
        as consumer c.removed (P.prefix (Q.capacity c.set) 0);
      let bad = consume_range c 1 n;
      rewrite consumer c.removed (P.prefix (Q.capacity c.set) n)
        as consumer c.removed (P.prefix n n);
      B.(consumed_bad := bad);
    };
  Task.await prod;
  Task.await cons;
  let all_new = B.(!produced_ok);
  let double_remove = B.(!consumed_bad);
  B.free produced_ok;
  B.free consumed_bad;
  rewrite producer c.produced n as producer c.produced (Q.capacity c.set);
  rewrite consumer c.removed (P.prefix n n)
    as consumer c.removed (P.prefix (Q.capacity c.set) (Q.capacity c.set));
  fold finished c;
  certify_empty c;
  let all_absent = check_empty_from c 1;
  (c, not all_new || double_remove || not all_absent)
}

(** Single-run convenience entry point. Native repeated runs must reuse a pool:
Task.teardown_pool marks logical completion but does not stop native workers. *)
divergent fn run (n:pos)
  returns result:(client & bool)
  ensures pure (Q.capacity (fst result).set == n /\ well_named (fst result) /\ not (snd result)) **
    finished (fst result)
{
  let pool = Task.setup_pool 2;
  let result = run_in_pool pool n;
  Task.teardown_pool pool;
  drop_ (Task.pool_done pool);
  result
}
