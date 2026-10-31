module Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.State
#lang-pulse

(**
Abstract-set authority and hand-over-hand traversal.

The implementation invariant contains only ghost state: half of the abstract
set and half of every node's shadow link. Physical links live under distinct
node locks. There is no global runtime mutex serializing set operations.

The predecessor stays locked until its successor has been locked. Agreement
then proves the successor is still live, even if other parts of the list have
changed. In particular, a removed node may be reused without relying on stale
pointer observations. This is the paper's lock-coupling argument, not a
lock-free traversal or a memory-reclamation argument.
*)

open Pulse.Lib.Pervasives
module S = FStar.Seq
module L = FStar.List.Tot
module G = Pulse.Lib.GhostReference
module N = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Storage
module H = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Model

type arena = cells:list N.cell { 2 <= L.length cells }
let bound (cells:arena) : nat = L.length cells - 2
type contents (cells:arena) = s:S.seq bool { S.length s == bound cells }

(** Registry and abstract model agree at every invariant opening. *)
let body (cells:arena) (g:G.ref (S.seq bool)) =
  exists* (s:contents cells).
    G.pts_to g #0.5R s ** N.shadows cells 0 (H.shadow s)

noeq type set = { cells:arena; model:G.ref (S.seq bool); name:iname }
let capacity (q:set) = bound q.cells
type key (q:set) = k:nat { 0 < k /\ k <= capacity q }
type node (q:set) = k:nat { k <= capacity q + 1 }
let is_set (q:set) = inv q.name (body q.cells q.model) ** N.accesses q.cells
let model (q:set) (s:S.seq bool) =
  G.pts_to q.model #0.5R s ** pure (S.length s == capacity q)
instance send_set q : is_send (is_set q) = FStar.Tactics.Typeclasses.solve
instance dup_set q : duplicable (is_set q) = FStar.Tactics.Typeclasses.solve

(** Preallocate the universe and initialize the single head-to-tail edge.
The set and its locks remain allocated; no destructor is claimed. *)
fn create (n:nat)
  returns q:set
  ensures pure (capacity q == n) ** is_set q ** model q (H.empty n)
{
  let initial:(nat -> nat) = (fun k -> if k = 0 then n + 1 else 0);
  let cells = N.allocate (n + 2) 0 initial;
  let g = G.alloc #(S.seq bool) (H.empty n);
  G.share g;
  H.empty_shadows n;
  N.shadows_ext cells 0 initial (H.shadow (H.empty n));
  fold body cells g;
  let name = new_invariant (body cells g);
  let q = { cells; model=g; name };
  rewrite each cells as q.cells;
  rewrite each g as q.model;
  rewrite each name as q.name;
  fold is_set q;
  fold model q (H.empty n);
  q
}

(** The head is permanently live, so its locked edge is a valid successor. *)
ghost fn head_valid (q:set) (v:nat)
  opens [q.name]
  preserves inv q.name (body q.cells q.model) **
    G.pts_to (N.at q.cells 0).N.shadow #0.5R v
  requires later_credit 1
  ensures pure (0 < v /\ v <= capacity q + 1)
{
  dup_inv q.name (body q.cells q.model);
  with_invariants_g unit emp_inames q.name (body q.cells q.model)
    (G.pts_to (N.at q.cells 0).N.shadow #0.5R v)
    (fun _ -> G.pts_to (N.at q.cells 0).N.shadow #0.5R v **
      pure (0 < v /\ v <= capacity q + 1)) fn _ {
    unfold body;
    with s. _;
    N.agree q.cells 0 (H.shadow s) 0 v;
    H.shadow_spec s 0;
    fold body q.cells q.model;
  };
}

(** A locked predecessor pins its successor until the latter is acquired.
This rules out retiring/reusing that successor during the hand-over. *)
ghost fn next_valid (q:set) (p:node q)
  (c:nat { p < c /\ c < capacity q + 1 }) (d:nat)
  opens [q.name]
  preserves inv q.name (body q.cells q.model) **
    G.pts_to (N.at q.cells p).N.shadow #0.5R c **
    G.pts_to (N.at q.cells c).N.shadow #0.5R d
  requires later_credit 1
  ensures pure (c < d /\ d <= capacity q + 1)
{
  dup_inv q.name (body q.cells q.model);
  with_invariants_g unit emp_inames q.name (body q.cells q.model)
    (G.pts_to (N.at q.cells p).N.shadow #0.5R c **
      G.pts_to (N.at q.cells c).N.shadow #0.5R d)
    (fun _ -> G.pts_to (N.at q.cells p).N.shadow #0.5R c **
      G.pts_to (N.at q.cells c).N.shadow #0.5R d **
      pure (c < d /\ d <= capacity q + 1)) fn _ {
    unfold body;
    with s. _;
    N.agree q.cells 0 (H.shadow s) p c;
    N.agree q.cells 0 (H.shadow s) c d;
    H.shadow_spec s p;
    H.shadow_spec s c;
    fold body q.cells q.model;
  };
}

divergent fn acquire_head (q:set)
  preserves is_set q
  returns c:(c:nat { 0 < c /\ c <= capacity q + 1 })
  ensures N.held (N.at q.cells 0) c
{
  unfold is_set;
  let c = N.acquire q.cells 0;
  unfold N.held;
  later_credit_buy 1;
  head_valid q c;
  fold N.held (N.at q.cells 0) c;
  fold is_set q;
  c
}

(** Acquire next before releasing current; at most two traversal locks are held. *)
divergent fn advance (q:set) (p:node q)
  (c:nat { p < c /\ c < capacity q + 1 })
  preserves is_set q
  requires N.held (N.at q.cells p) c
  returns d:(d:nat { c < d /\ d <= capacity q + 1 })
  ensures N.held (N.at q.cells c) d
{
  unfold is_set;
  let d = N.acquire q.cells c;
  unfold N.held (N.at q.cells p) c;
  unfold N.held (N.at q.cells c) d;
  later_credit_buy 1;
  next_valid q p c d;
  fold N.held (N.at q.cells p) c;
  fold N.held (N.at q.cells c) d;
  N.release q.cells p;
  fold is_set q;
  d
}

(** The returned locked window brackets k, not merely its location at entry.
Blocking lock acquisition makes this a partial-correctness contract. *)
divergent fn rec locate_from (q:set) (k:key q)
  (p:nat { p < k }) (c:nat { p < c /\ c <= capacity q + 1 })
  preserves is_set q
  requires N.held (N.at q.cells p) c
  returns w:(w:(nat & nat) { fst w < k /\ k <= snd w /\ snd w <= capacity q + 1 })
  ensures N.held (N.at q.cells (fst w)) (snd w)
{
  if (c < k) {
    let d = advance q p c;
    locate_from q k c d
  } else {
    (p, c)
  }
}

divergent fn locate (q:set) (k:key q)
  preserves is_set q
  returns w:(w:(nat & nat) { fst w < k /\ k <= snd w /\ snd w <= capacity q + 1 })
  ensures N.held (N.at q.cells (fst w)) (snd w)
{
  let c = acquire_head q;
  locate_from q k 0 c
}

fn unlock (q:set) (p:node q) (#c:erased nat)
  preserves is_set q
  requires N.held (N.at q.cells p) c
{
  unfold is_set;
  N.release q.cells p;
  fold is_set q;
}
