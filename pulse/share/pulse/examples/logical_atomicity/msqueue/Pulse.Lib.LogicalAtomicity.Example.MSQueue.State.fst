module Pulse.Lib.LogicalAtomicity.Example.MSQueue.State
#lang-pulse

(**
Representation invariant and stable observations for the Michael--Scott queue.

The implementation invariant couples physical head/tail and all next fields
to an authoritative monotonic history, half of a ghost FIFO sequence, and
the payload resources for that sequence. A client owns the other model half.
An operation opens its client AU and this implementation invariant around
one primitive; agreement identifies the abstract and concrete state at that
step, and combining both halves permits updating the model on commitment.

Snapshots record historical facts, not permission to assume a pointer is
still current. Prefix stability preserves node identity and links; CAS
success then establishes currentness. This is analogous to authoritative
ghost state plus persistent observations in Iris, implemented with existing
Pulse ghost references rather than a new resource algebra.

Retaining every link and forbidding node reuse is essential to this proof.
There is no queue destructor, reclamation, prophecy, or progress theorem.
Tail helping changes representation only; it does not execute another
operation's client continuation (compare the separate Helping example).
*)

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module G = Pulse.Lib.GhostReference
module MR = Pulse.Lib.MonotonicGhostRef
module U32 = FStar.UInt32
module S = FStar.Seq
module H = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Model
module N = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Storage
module Atom = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Atomics

(** Valid pure history over IDs belonging to this arena. *)
type history (cells:N.arena) = s:H.state (N.id cells) { H.valid s }
(** A loaded next pointer is either null or an in-bounds ID; head/tail loads
are more precise and always return an ID. *)
type pointer (cells:N.arena) =
  n:U32.t { n == N.null \/ U32.v n < FStar.List.Tot.length cells }

(** Physical pointer boxes and ghost authorities. The history authority
supports stale snapshots; the model reference supports client agreement. *)
noeq type core (cells:N.arena) = {
  head:B.box U32.t;
  tail:B.box U32.t;
  history:MR.mref (H.advances #(N.id cells));
  model:G.ref (S.seq U32.t);
}

(** Abstract value sequence after the current dummy, independent of tail lag. *)
let contents (#cells:N.arena) (s:history cells) = H.contents (N.value cells) s

(** Full representation at s: pointer values, history authority, internal
model half, retained physical links, and ownership of only the LIVE payloads.
Dequeue removes a payload here without releasing its node's physical link. *)
let state (#cells:N.arena) (c:core cells) (p:U32.t -> slprop) (s:history cells) =
  B.pts_to c.head (S.index s.H.nodes s.H.head) **
  B.pts_to c.tail (S.index s.H.nodes s.H.tail) **
  MR.pts_to c.history #1.0R s **
  G.pts_to c.model #0.5R (contents s) **
  N.links cells s.H.nodes **
  N.payloads p (S.seq_to_list (contents s))

(** Hide the current history behind the implementation invariant. *)
let queue_inv (#cells:N.arena) (c:core cells) (p:U32.t -> slprop) =
  exists* (s:history cells). state c p s

(** Runtime/ghost handle; owning this record alone grants no field access. *)
noeq type queue (cells:N.arena) = { core:core cells; name:iname }

(** Shareable invariant handle for a fixed payload interpretation P. *)
let is_queue (#cells:N.arena) (q:queue cells) (p:U32.t -> slprop) =
  inv q.name (queue_inv q.core p)

(** Send the handle when every queued payload can cross thread localities.
This does not make arbitrary client atomic updates sendable. *)
instance send_queue (#cells:N.arena) q p {| (x:U32.t -> is_send (p x)) |}
  : is_send (is_queue #cells q p) = FStar.Tactics.Typeclasses.solve

(** Client half of the abstract state. Agreement with the invariant half
identifies xs at an attempt; neither half alone can change the sequence. *)
let model (#cells:N.arena) (q:queue cells) (xs:S.seq U32.t) =
  G.pts_to q.core.model #0.5R xs

(** A node was head or tail in the particular historical state s. *)
let position (#cells:N.arena) (s:history cells) (head:bool) (n:N.id cells) =
  pure (n == S.index s.H.nodes (if head then s.H.head else s.H.tail))

(** Persistent historical pointer observation. It is not a claim that n
remains the current pointer when later code executes. *)
let observed (#cells:N.arena) (q:queue cells) (head:bool) (n:N.id cells) =
  exists* (s:history cells). MR.snapshot q.core.history s ** position s head n

(** Consecutive history nodes with the first at or behind tail. The bound
is used to show that a successful helping CAS advances tail by one. *)
let adjacent (#cells:N.arena) (s:history cells) (k:nat) (n next:N.id cells) =
  pure (k <= s.H.tail /\ k + 1 < S.length s.H.nodes /\
    n == S.index s.H.nodes k /\ next == S.index s.H.nodes (k + 1))

(** Persistent evidence of a published edge. It remains meaningful after
the nodes are retired because history and physical links are never reclaimed. *)
let edge (#cells:N.arena) (q:queue cells) (n next:N.id cells) =
  exists* (s:history cells) (k:nat).
    MR.snapshot q.core.history s ** adjacent s k n next

(** Consume node zero as dummy, allocate pointer/model state, and return an
empty abstract model. Other node tickets stay with the caller for enqueues. *)
fn create (cells:N.arena) (p:U32.t -> slprop)
  requires N.ticket cells 0ul
  returns q:queue cells
  ensures is_queue q p ** model q S.empty
{
  let head = B.alloc 0ul;
  let tail = B.alloc 0ul;
  let history = MR.alloc #(H.state (N.id cells)) #H.advances (H.singleton 0ul);
  let g = G.alloc #(S.seq U32.t) S.empty;
  G.share g;
  N.singleton cells 0ul;
  let c = { head; tail; history; model=g };
  H.contents_length (N.value cells) (H.singleton 0ul);
  S.lemma_empty (contents (H.singleton (0ul <: N.id cells)));
  assert pure (contents (H.singleton (0ul <: N.id cells)) == S.empty);
  fold N.payloads p [];
  rewrite N.payloads p [] as N.payloads p (S.seq_to_list (contents (H.singleton (0ul <: N.id cells))));
  rewrite each head as c.head;
  rewrite each tail as c.tail;
  rewrite each history as c.history;
  rewrite each g as c.model;
  fold state c p (H.singleton 0ul);
  fold queue_inv c p;
  let name = new_invariant (queue_inv c p);
  let q = { core=c; name };
  rewrite each c as q.core;
  rewrite each name as q.name;
  fold is_queue q p;
  fold model q S.empty;
  q
}

(** Read one pointer and record its current history snapshot. Ordinary
lexical invariant opening suffices: no client AU is committed by this read. *)
fn read_pointer (#cells:N.arena) (q:queue cells) (p:U32.t -> slprop) (head:bool)
  preserves is_queue q p
  returns n:N.id cells
  ensures observed q head n
{
  unfold is_queue;
  dup_inv q.name (queue_inv q.core p);
  let n = with_invariants (N.id cells) emp_inames q.name (queue_inv q.core p)
    emp (fun n -> observed q head n) fn _ {
    unfold queue_inv;
    with s. unfold state q.core p s;
    let n = if head {
      Atom.read q.core.head
    } else {
      Atom.read q.core.tail
    };
    MR.take_snapshot q.core.history s;
    fold position s head n;
    fold observed q head n;
    fold state q.core p s;
    fold queue_inv q.core p;
    n
  };
  fold is_queue q p;
  n
}

(** Read next at a historically observed tail. A non-null result yields
an immutable edge; null returns the old observation, not a promise that
the tail will still be last at a later CAS. Used by enqueue, not empty dequeue. *)
fn read_successor (#cells:N.arena) (q:queue cells) (p:U32.t -> slprop) (tail:N.id cells)
  preserves is_queue q p
  requires observed q false tail
  returns n:pointer cells
  ensures (if n == N.null then observed q false tail else edge q tail n)
{
  unfold is_queue;
  dup_inv q.name (queue_inv q.core p);
  let n = with_invariants (pointer cells) emp_inames q.name (queue_inv q.core p)
    (observed q false tail)
    (fun n -> if n == N.null then observed q false tail else edge q tail n) fn _ {
    unfold queue_inv;
    with s. unfold state q.core p s;
    unfold observed;
    with old. _;
    unfold position;
    dup (MR.snapshot q.core.history old) ();
    MR.recall_snapshot q.core.history;
    N.focus cells s.H.nodes old.H.tail;
    rewrite each (S.index s.H.nodes old.H.tail) as tail;
    let n = Atom.read (N.at cells tail).N.next;
    rewrite B.pts_to (N.at cells tail).N.next (N.successor cells s.H.nodes old.H.tail)
      as B.pts_to (N.at cells (S.index s.H.nodes old.H.tail)).N.next
        (N.successor cells s.H.nodes old.H.tail);
    N.restore cells s.H.nodes old.H.tail;
    MR.take_snapshot q.core.history s;
    if (n = N.null) {
      fold position old false tail;
      fold observed q false tail;
      rewrite observed q false tail as
        (if n == N.null then observed q false tail else edge q tail n);
    } else {
      drop_ (MR.snapshot q.core.history old);
      fold adjacent s old.H.tail tail n;
      fold edge q tail n;
      rewrite edge q tail n as
        (if n == N.null then observed q false tail else edge q tail n);
    };
    fold state q.core p s;
    fold queue_inv q.core p;
    n
  };
  fold is_queue q p;
  n
}

(** Best-effort structural CAS along a known edge. On success uniqueness
identifies the current tail index and permits advance_tail. Failure may be
staleness or spurious failure; neither branch changes the abstract FIFO. *)
fn help_tail (#cells:N.arena) (q:queue cells) (p:U32.t -> slprop) (tail next:N.id cells)
  preserves is_queue q p
  requires edge q tail next
  returns moved:bool
{
  unfold is_queue;
  dup_inv q.name (queue_inv q.core p);
  let moved = with_invariants bool emp_inames q.name (queue_inv q.core p)
    (edge q tail next) (fun _ -> emp) fn _ {
    unfold queue_inv;
    with s. unfold state q.core p s;
    unfold edge;
    with old k. _;
    unfold adjacent;
    MR.recall_snapshot q.core.history;
    let moved = Atom.cas q.core.tail tail next;
    if moved {
      elim_cond_true _ _ _;
      H.same_node_same_index old s k s.H.tail;
      MR.update q.core.history (H.advance_tail s);
      assert pure (contents s == contents (H.advance_tail s));
      rewrite N.payloads p (S.seq_to_list (contents s))
        as N.payloads p (S.seq_to_list (contents (H.advance_tail s)));
      fold state q.core p (H.advance_tail s);
    } else {
      elim_cond_false _ _ _;
      fold state q.core p s;
    };
    fold queue_inv q.core p;
    moved
  };
  fold is_queue q p;
  moved
}

(** Strengthen adjacency with a strict tail bound, permitting a head advance
at k without overtaking tail. *)
let ahead_at (#cells:N.arena) (s:history cells) (k:nat) (n next:N.id cells) =
  adjacent s k n next ** pure (k < s.H.tail)

(** Persistent tail-ahead certificate; monotone tail motion preserves its
bound until a successful head CAS can identify the relevant current index. *)
let ahead (#cells:N.arena) (q:queue cells) (n next:N.id cells) =
  exists* (s:history cells) (k:nat).
    MR.snapshot q.core.history s ** ahead_at s k n next

(** Read tail after observing a head edge. Inequality with the old head
strengthens edge to ahead; equality means the caller should help tail and
retry. No current-head assertion is made without the subsequent head CAS. *)
fn tail_ahead (#cells:N.arena) (q:queue cells) (p:U32.t -> slprop) (head next:N.id cells)
  preserves is_queue q p
  requires edge q head next
  returns ready:bool
  ensures (if ready then ahead q head next else edge q head next)
{
  unfold is_queue;
  dup_inv q.name (queue_inv q.core p);
  let ready = with_invariants bool emp_inames q.name (queue_inv q.core p)
    (edge q head next) (fun ready -> if ready then ahead q head next else edge q head next) fn _ {
    unfold queue_inv;
    with s. unfold state q.core p s;
    unfold edge;
    with old k. _;
    unfold adjacent old k head next;
    MR.recall_snapshot q.core.history;
    let tail = Atom.read q.core.tail;
    MR.take_snapshot q.core.history s;
    fold adjacent s k head next;
    if (tail = head) {
      fold edge q head next;
      fold state q.core p s;
      fold queue_inv q.core p;
      false
    } else {
      fold ahead_at s k head next;
      fold ahead q head next;
      fold state q.core p s;
      fold queue_inv q.core p;
      true
    }
  };
  fold is_queue q p;
  ready
}
