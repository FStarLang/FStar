module Pulse.Lib.LogicalAtomicity.Example.MSQueue.Enqueue
#lang-pulse

(**
Logically atomic enqueue with payload ownership transfer.

The abstract transition is xs -> xs ++ [value n]. The operation separately
receives a fresh node ticket and P(value n); these resources enter the queue
ONLY at successful null-to-n CAS on the old last node's next field. This
link CAS is the linearization point. The following tail CAS is optional
representation maintenance and never changes the abstract sequence.

During the link attempt, the client AU exposes its model half and the
implementation invariant exposes the other half. Agreement identifies xs;
success updates both, appends the payload, and commits the continuation.
Failure restores the AU, ticket, and payload without refunding credits.
The delayed closing update lets the lexical implementation invariant close
before the explicit client mask is restored.

This is the Iris-style AU protocol applied to a multi-step implementation,
not an atomic block around the loop. Helping advances other producers' tail
pointers but does not execute their client continuations. The arena is
finite and non-reusing; no termination, reclamation, or lock-freedom theorem
is provided. See README.md in the foundation directory for scope/references.
*)

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module G = Pulse.Lib.GhostReference
module MR = Pulse.Lib.MonotonicGhostRef
module U32 = FStar.UInt32
module S = FStar.Seq
module H = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Model
module N = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Storage
module Q = Pulse.Lib.LogicalAtomicity.Example.MSQueue.State
module D = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Actions
module M = Pulse.Lib.LogicalAtomicity.Masks
module A = Pulse.Lib.LogicalAtomicity.Atomic
module U = Pulse.Lib.LogicalAtomicity.Update
module Atom = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Atomics

(** Strong FIFO enqueue post-state, indexed by the state at commitment.
Payload ownership is tracked separately in resources and the queue invariant. *)
let beta (#cells:N.arena) (q:Q.queue cells) (n:N.id cells) (xs:S.seq U32.t) (_:unit) =
  Q.model q (S.append xs (S.create 1 (N.value cells n)))

(** Client AU for appending this node's immutable value. The client chooses
its open mask, per-attempt credit cost, and eventual continuation phi. *)
let update (#cells:N.arena) (q:Q.queue cells) (n:N.id cells)
  inner credits (phi:unit -> slprop) =
  A.atomic_update emp_inames inner credits (Q.model q) (beta q n) (fun _ _ -> phi ())

(** One current abstract model plus an additive abort/commit choice. *)
let opened (#cells:N.arena) (q:Q.queue cells) (n:N.id cells) inner credits phi =
  A.opened emp_inames inner (Q.model q) (update q n inner credits phi)
    (beta q n) (fun _ _ -> phi ())

(** Closing obligation specialized to this attempt's xs. *)
let closing (#cells:N.arena) (q:Q.queue cells) (n:N.id cells) inner credits phi xs =
  A.closing emp_inames inner (Q.model q) (update q n inner credits phi)
    (beta q n) (fun _ _ -> phi ()) xs

(** Implementation-side input: handle, opening credit, stale-tail evidence,
and ownership to transfer. None of these asserts that tail is still current. *)
let resources (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop) (tail n:N.id cells) =
  Q.is_queue q p ** later_credit 1 ** Q.observed q false tail **
  N.ticket cells n ** p (N.value cells n)

(** Success delivers phi and an edge usable for tail helping. Failure returns
all untransferred ownership and the AU, allowing an ordinary-code retry. *)
let attempt_post (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop)
  (tail n:N.id cells) inner credits phi (ok:bool) =
  if ok then phi () ** Q.edge q tail n
  else update q n inner credits phi ** (N.ticket cells n ** p (N.value cells n))

(** The single-step linearization proof. Freshness follows from the ticket;
CAS success proves the observed next field was the current final link.
Rebuild links, payloads, and both model halves before suspending commit.
On failure, restore the focused link and suspend abort instead. *)
atomic fn link_opened (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop)
  (tail n:N.id cells) (inner:inames) (credits:nat) (phi:unit -> slprop)
  opens [q.Q.name]
  requires opened q n inner credits phi ** resources q p tail n
  returns ok:bool
  ensures U.fupd inner emp_inames (attempt_post q p tail n inner credits phi ok) **
    Q.is_queue q p
{
  unfold resources;
  unfold Q.is_queue;
  dup_inv q.Q.name (Q.queue_inv q.Q.core p);
  let ok = with_invariants_a bool emp_inames q.Q.name (Q.queue_inv q.Q.core p)
    (opened q n inner credits phi ** Q.observed q false tail **
      N.ticket cells n ** p (N.value cells n))
    (fun ok -> U.fupd inner emp_inames (attempt_post q p tail n inner credits phi ok)) fn _ {
    unfold Q.queue_inv;
    with s. unfold Q.state q.Q.core p s;
    unfold Q.observed;
    with old. _;
    unfold Q.position old false tail;
    MR.recall_snapshot q.Q.core.Q.history;
    N.ticket_is_fresh cells s.H.nodes n;
    N.focus cells s.H.nodes old.H.tail;
    rewrite each (S.index s.H.nodes old.H.tail) as tail;
    unfold opened;
    unfold A.opened;
    with xs. _;
    unfold Q.model q xs;
    G.pts_to_injective_eq q.Q.core.Q.model;
    let ok = Atom.cas (N.at cells tail).N.next N.null n;
    if ok {
      elim_cond_true _ _ _;
      assert pure (old.H.tail + 1 == S.length s.H.nodes);
      let next:erased (Q.history cells) = hide (H.append s n);
      rewrite N.rest cells s.H.nodes old.H.tail
        as N.rest cells s.H.nodes (S.length s.H.nodes - 1);
      rewrite B.pts_to (N.at cells tail).N.next n
        as B.pts_to (N.at cells (S.index s.H.nodes (S.length s.H.nodes - 1))).N.next n;
      N.append_link cells s.H.nodes n;
      rewrite N.links cells (S.append s.H.nodes (S.create 1 n)) as N.links cells next.H.nodes;
      MR.update q.Q.core.Q.history next;
      H.append_contents (N.value cells) s n;
      H.to_list_append (Q.contents s) (S.create 1 (N.value cells n));
      H.to_list_singleton (N.value cells n);
      N.append_payload p (S.seq_to_list (Q.contents s)) (N.value cells n);
      rewrite N.payloads p (FStar.List.Tot.append (S.seq_to_list (Q.contents s)) [N.value cells n])
        as N.payloads p (S.seq_to_list (Q.contents next));
      G.gather q.Q.core.Q.model;
      G.write q.Q.core.Q.model (Q.contents next);
      G.share q.Q.core.Q.model;
      rewrite each (1.0R /. 2.0R) as 0.5R;
      fold Q.model q (S.append xs (S.create 1 (N.value cells n)));
      fold beta q n xs ();
      fold closing q n inner credits phi xs;
      MR.take_snapshot q.Q.core.Q.history next;
      fold Q.adjacent next old.H.tail tail n;
      fold Q.edge q tail n;
      fold Q.state q.Q.core p next;
      fold Q.queue_inv q.Q.core p;
      D.delay inner
        ((closing q n inner credits phi xs ** beta q n xs ()) ** Q.edge q tail n)
        (attempt_post q p tail n inner credits phi true)
        (fun _ -> M.frame_ghost (Q.edge q tail n)
          (A.commit emp_inames inner (Q.model q) (update q n inner credits phi)
            (beta q n) (fun _ _ -> phi ()) xs ()));
      true
    } else {
      elim_cond_false _ _ _;
      rewrite B.pts_to (N.at cells tail).N.next (N.successor cells s.H.nodes old.H.tail)
        as B.pts_to (N.at cells (S.index s.H.nodes old.H.tail)).N.next
          (N.successor cells s.H.nodes old.H.tail);
      N.restore cells s.H.nodes old.H.tail;
      fold Q.model q xs;
      fold A.opened emp_inames inner (Q.model q) (update q n inner credits phi)
        (beta q n) (fun _ _ -> phi ());
      fold opened q n inner credits phi;
      fold Q.state q.Q.core p s;
      fold Q.queue_inv q.Q.core p;
      D.delay inner
        (opened q n inner credits phi ** (N.ticket cells n ** p (N.value cells n)))
        (attempt_post q p tail n inner credits phi false)
        (fun _ -> M.frame_ghost (N.ticket cells n ** p (N.value cells n))
          (A.abort_opened emp_inames inner (Q.model q) (update q n inner credits phi)
            (beta q n) (fun _ _ -> phi ())));
      false
    }
  };
  fold Q.is_queue q p;
  ok
}

(** Fund both openings and combine them through Actions.with_update.
The client-open mask must exclude q.name; otherwise the implementation
invariant could be opened twice. Failure still spends this attempt's credits. *)
fn try_link (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop)
  (tail n:N.id cells) (inner:inames { not (mem_inv inner q.Q.name) })
  (credits:nat) (phi:unit -> slprop)
  preserves Q.is_queue q p
  requires update q n inner credits phi ** N.ticket cells n ** p (N.value cells n) **
    Q.observed q false tail
  returns ok:bool
  ensures attempt_post q p tail n inner credits phi ok
{
  later_credit_buy credits;
  later_credit_buy 1;
  fold resources q p tail n;
  unfold update;
  slprop_equivs ();
  D.with_update inner (add_inv emp_inames q.Q.name) credits (Q.model q) (beta q n)
    (fun _ _ -> phi ()) (resources q p tail n) (Q.is_queue q p)
    (attempt_post q p tail n inner credits phi)
    (fun _ -> link_opened q p tail n inner credits phi)
}

(** Public retrying enqueue. Help a non-final observed tail, retry failed
link CAS, and best-effort advance tail after commitment. Returning implies
phi and ownership transfer, but no bound on retries or pool exhaustion policy
is specified: the caller must already supply an unused node. *)
divergent fn rec enqueue (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop)
  (n:N.id cells) (inner:inames { not (mem_inv inner q.Q.name) })
  (credits:nat) (phi:unit -> slprop)
  preserves Q.is_queue q p
  requires update q n inner credits phi ** N.ticket cells n ** p (N.value cells n)
  ensures phi ()
{
  let tail = Q.read_pointer q p false;
  let next = Q.read_successor q p tail;
  if (next = N.null) {
    rewrite (if next == N.null then Q.observed q false tail else Q.edge q tail next)
      as Q.observed q false tail;
    let ok = try_link q p tail n inner credits phi;
    unfold attempt_post;
    if ok {
      let _ = Q.help_tail q p tail n;
    } else {
      enqueue q p n inner credits phi;
    }
  } else {
    rewrite (if next == N.null then Q.observed q false tail else Q.edge q tail next)
      as Q.edge q tail next;
    let _ = Q.help_tail q p tail next;
    enqueue q p n inner credits phi;
  }
}
