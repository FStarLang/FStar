module Pulse.Lib.LogicalAtomicity.Example.MSQueue.Dequeue
#lang-pulse

(**
Logically atomic FIFO dequeue, including empty results and payload recovery.

There are two linearization points. A null-successor load at an observed
head commits None and proves the abstract queue empty AT THAT LOAD. A
successful head CAS commits Some v, removes the first abstract value, and
returns its exclusive P v. A non-null successor load is only speculative:
it aborts its AU and returns a stable edge for a later attempt.

The order is head load, next load, then tail load. Monotonic snapshots prove
that an old head with null next must still be the current dummy; a tail-ahead
certificate makes a later successful head CAS safe. Thus this variant does
not need a second head-validation load or prophecy. Non-reuse and permanently
retained links are essential; the proof does not cover reclamation or ABA.

All commits/aborts use one additive AU closing choice and defer its execution
until the lexical implementation invariant is restored. Tail helping does
not commit the dequeue. The operation has partial-correctness guarantees,
not wait-freedom, lock-freedom, or eventual success under spurious failure.
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

(** Exact abstract result: None proves emptiness; Some v splits xs as v::ys,
returns P v, and changes the model to ys. This establishes FIFO order and
ownership transfer, not merely membership or memory safety. *)
let beta (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop)
  (xs:S.seq U32.t) (result:option U32.t) =
  match result with
  | None -> Q.model q xs ** pure (S.length xs == 0)
  | Some v -> exists* ys.
      Q.model q ys ** p v ** pure (xs == S.cons v ys)

(** Client-supplied retryable transition from a model xs to beta xs result,
with phi determining what ownership the caller receives after commitment. *)
let update (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop)
  inner credits (phi:option U32.t -> slprop) =
  A.atomic_update emp_inames inner credits (Q.model q) (beta q p) (fun _ y -> phi y)

(** One attempt's model ownership and its additive closing choice. *)
let opened (#cells:N.arena) (q:Q.queue cells) p inner credits phi =
  A.opened emp_inames inner (Q.model q) (update q p inner credits phi)
    (beta q p) (fun _ y -> phi y)

(** Closing capability tied to the abstract sequence exposed this attempt. *)
let closing (#cells:N.arena) (q:Q.queue cells) p inner credits phi xs =
  A.closing emp_inames inner (Q.model q) (update q p inner credits phi)
    (beta q p) (fun _ y -> phi y) xs

(** Handle, one implementation-invariant credit, and historical head evidence
for the next-field read; currentness is proved only in its null branch. *)
let read_resources (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop) (head:N.id cells) =
  Q.is_queue q p ** later_credit 1 ** Q.observed q true head

(** Null finishes the operation with phi None. Non-null returns the AU and
an edge; it does not yet remove or grant ownership of the successor payload. *)
let read_post (#cells:N.arena) (q:Q.queue cells) p (head:N.id cells)
  inner credits phi (next:Q.pointer cells) =
  if next == N.null then phi None
  else update q p inner credits phi ** Q.edge q head next

(** One next-field load with client and implementation state related by
ghost-half agreement. Use empty_from_head_snapshot to commit an empty result,
or preserve the model and abort after recording a non-null edge. *)
atomic fn read_opened (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop)
  (head:N.id cells) (inner:inames) (credits:nat) (phi:option U32.t -> slprop)
  opens [q.Q.name]
  requires opened q p inner credits phi ** read_resources q p head
  returns next:Q.pointer cells
  ensures U.fupd inner emp_inames (read_post q p head inner credits phi next) ** Q.is_queue q p
{
  unfold read_resources;
  unfold Q.is_queue;
  dup_inv q.Q.name (Q.queue_inv q.Q.core p);
  let next = with_invariants_a (Q.pointer cells) emp_inames q.Q.name (Q.queue_inv q.Q.core p)
    (opened q p inner credits phi ** Q.observed q true head)
    (fun next -> U.fupd inner emp_inames (read_post q p head inner credits phi next)) fn _ {
    unfold Q.queue_inv;
    with s. unfold Q.state q.Q.core p s;
    unfold Q.observed;
    with old. _;
    unfold Q.position old true head;
    MR.recall_snapshot q.Q.core.Q.history;
    unfold opened;
    unfold A.opened;
    with xs. _;
    unfold Q.model q xs;
    G.pts_to_injective_eq q.Q.core.Q.model;
    N.focus cells s.H.nodes old.H.head;
    rewrite each (S.index s.H.nodes old.H.head) as head;
    let next = Atom.read (N.at cells head).N.next;
    rewrite B.pts_to (N.at cells head).N.next (N.successor cells s.H.nodes old.H.head)
      as B.pts_to (N.at cells (S.index s.H.nodes old.H.head)).N.next
        (N.successor cells s.H.nodes old.H.head);
    N.restore cells s.H.nodes old.H.head;
    MR.take_snapshot q.Q.core.Q.history s;
    fold Q.model q xs;
    fold Q.state q.Q.core p s;
    fold Q.queue_inv q.Q.core p;
    if (next = N.null) {
      H.empty_from_head_snapshot old s;
      H.contents_length (N.value cells) s;
      fold beta q p xs None;
      fold closing q p inner credits phi xs;
      D.delay inner (closing q p inner credits phi xs ** beta q p xs None) (phi None)
        (fun _ -> A.commit emp_inames inner (Q.model q) (update q p inner credits phi)
          (beta q p) (fun _ y -> phi y) xs None);
      rewrite U.fupd inner emp_inames (phi None)
        as U.fupd inner emp_inames (read_post q p head inner credits phi next);
      next
    } else {
      fold Q.adjacent s old.H.head head next;
      fold Q.edge q head next;
      fold A.opened emp_inames inner (Q.model q) (update q p inner credits phi)
        (beta q p) (fun _ y -> phi y);
      fold opened q p inner credits phi;
      D.delay inner (opened q p inner credits phi ** Q.edge q head next)
        (update q p inner credits phi ** Q.edge q head next)
        (fun _ -> M.frame_ghost (Q.edge q head next)
          (A.abort_opened emp_inames inner (Q.model q) (update q p inner credits phi)
            (beta q p) (fun _ y -> phi y)));
      rewrite U.fupd inner emp_inames (update q p inner credits phi ** Q.edge q head next)
        as U.fupd inner emp_inames (read_post q p head inner credits phi next);
      next
    }
  };
  fold Q.is_queue q p;
  next
}

(** Supply fresh AU and implementation credits for the potentially
linearizing load, enforcing disjoint client/implementation invariant masks. *)
fn read_head_successor (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop)
  (head:N.id cells) (inner:inames { not (mem_inv inner q.Q.name) })
  (credits:nat) (phi:option U32.t -> slprop)
  preserves Q.is_queue q p
  requires update q p inner credits phi ** Q.observed q true head
  returns next:Q.pointer cells
  ensures read_post q p head inner credits phi next
{
  later_credit_buy credits;
  later_credit_buy 1;
  fold read_resources q p head;
  unfold update;
  slprop_equivs ();
  D.with_update inner (add_inv emp_inames q.Q.name) credits (Q.model q) (beta q p)
    (fun _ y -> phi y) (read_resources q p head) (Q.is_queue q p)
    (read_post q p head inner credits phi)
    (fun _ -> read_opened q p head inner credits phi)
}

(** A head CAS needs the stronger ahead certificate, not only an edge:
the new dummy must not overtake the current tail. *)
let cas_resources (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop) (head next:N.id cells) =
  Q.is_queue q p ** later_credit 1 ** Q.ahead q head next

(** Success delivers the committed value's phi; failure restores the AU
without falsely returning a payload from a lost race. *)
let cas_post (#cells:N.arena) (q:Q.queue cells) p (next:N.id cells) inner credits phi (ok:bool) =
  if ok then phi (Some (N.value cells next)) else update q p inner credits phi

(** Nonempty-dequeue linearization proof. CAS equality and unique history
identify the current head; remove_contents proves exact FIFO removal.
Return the first payload, retain every link, update both model halves, and
delay commit. A failed CAS leaves all queue payloads in the invariant. *)
atomic fn cas_opened (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop)
  (head next:N.id cells) (inner:inames) (credits:nat) (phi:option U32.t -> slprop)
  opens [q.Q.name]
  requires opened q p inner credits phi ** cas_resources q p head next
  returns ok:bool
  ensures U.fupd inner emp_inames (cas_post q p next inner credits phi ok) ** Q.is_queue q p
{
  unfold cas_resources;
  unfold Q.is_queue;
  dup_inv q.Q.name (Q.queue_inv q.Q.core p);
  let ok = with_invariants_a bool emp_inames q.Q.name (Q.queue_inv q.Q.core p)
    (opened q p inner credits phi ** Q.ahead q head next)
    (fun ok -> U.fupd inner emp_inames (cas_post q p next inner credits phi ok)) fn _ {
    unfold Q.queue_inv;
    with s. unfold Q.state q.Q.core p s;
    unfold Q.ahead;
    with old k. _;
    unfold Q.ahead_at old k head next;
    unfold Q.adjacent old k head next;
    MR.recall_snapshot q.Q.core.Q.history;
    unfold opened;
    unfold A.opened;
    with xs. _;
    unfold Q.model q xs;
    G.pts_to_injective_eq q.Q.core.Q.model;
    let ok = Atom.cas q.Q.core.Q.head head next;
    if ok {
      elim_cond_true _ _ _;
      H.same_node_same_index old s k s.H.head;
      let after:erased (Q.history cells) = hide (H.advance_head s);
      H.remove_contents (N.value cells) s;
      S.lemma_seq_to_list_cons (N.value cells next) (Q.contents after);
      rewrite N.payloads p (S.seq_to_list (Q.contents s))
        as N.payloads p (N.value cells next :: S.seq_to_list (Q.contents after));
      unfold N.payloads p (N.value cells next :: S.seq_to_list (Q.contents after));
      MR.update q.Q.core.Q.history after;
      G.gather q.Q.core.Q.model;
      G.write q.Q.core.Q.model (Q.contents after);
      G.share q.Q.core.Q.model;
      rewrite each (1.0R /. 2.0R) as 0.5R;
      rewrite N.links cells s.H.nodes as N.links cells after.H.nodes;
      fold Q.state q.Q.core p after;
      fold Q.queue_inv q.Q.core p;
      fold Q.model q (Q.contents after);
      fold beta q p xs (Some (N.value cells next));
      fold closing q p inner credits phi xs;
      D.delay inner (closing q p inner credits phi xs ** beta q p xs (Some (N.value cells next)))
        (cas_post q p next inner credits phi true)
        (fun _ -> A.commit emp_inames inner (Q.model q) (update q p inner credits phi)
          (beta q p) (fun _ y -> phi y) xs (Some (N.value cells next)));
      true
    } else {
      elim_cond_false _ _ _;
      fold Q.model q xs;
      fold Q.state q.Q.core p s;
      fold Q.queue_inv q.Q.core p;
      fold A.opened emp_inames inner (Q.model q) (update q p inner credits phi)
        (beta q p) (fun _ y -> phi y);
      fold opened q p inner credits phi;
      D.delay inner (opened q p inner credits phi) (cas_post q p next inner credits phi false)
        (fun _ -> A.abort_opened emp_inames inner (Q.model q) (update q p inner credits phi)
          (beta q p) (fun _ y -> phi y));
      false
    }
  };
  fold Q.is_queue q p;
  ok
}

(** Fund and execute one head-CAS attempt, with no credit refund on abort. *)
fn try_advance (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop)
  (head next:N.id cells) (inner:inames { not (mem_inv inner q.Q.name) })
  (credits:nat) (phi:option U32.t -> slprop)
  preserves Q.is_queue q p
  requires update q p inner credits phi ** Q.ahead q head next
  returns ok:bool
  ensures cas_post q p next inner credits phi ok
{
  later_credit_buy credits;
  later_credit_buy 1;
  fold cas_resources q p head next;
  unfold update;
  slprop_equivs ();
  D.with_update inner (add_inv emp_inames q.Q.name) credits (Q.model q) (beta q p)
    (fun _ y -> phi y) (cas_resources q p head next) (Q.is_queue q p)
    (cas_post q p next inner credits phi)
    (fun _ -> cas_opened q p head next inner credits phi)
}

(** Public dequeue loop: return after an empty-read or head-CAS commit;
otherwise help a lagging tail or retry a lost CAS race. None describes an
empty instant during the call, not necessarily the queue at return time. *)
divergent fn rec dequeue (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop)
  (inner:inames { not (mem_inv inner q.Q.name) }) (credits:nat) (phi:option U32.t -> slprop)
  preserves Q.is_queue q p
  requires update q p inner credits phi
  returns result:option U32.t
  ensures phi result
{
  let head = Q.read_pointer q p true;
  let next = read_head_successor q p head inner credits phi;
  unfold read_post q p head inner credits phi next;
  if (next = N.null) {
    rewrite (if next == N.null then phi None else update q p inner credits phi ** Q.edge q head next)
      as phi None;
    None
  } else {
    rewrite (if next == N.null then phi None else update q p inner credits phi ** Q.edge q head next)
      as (update q p inner credits phi ** Q.edge q head next);
    let ready = Q.tail_ahead q p head next;
    if ready {
      let ok = try_advance q p head next inner credits phi;
      unfold cas_post q p next inner credits phi ok;
      if ok {
        Some (N.value cells next)
      } else {
        dequeue q p inner credits phi
      }
    } else {
      let _ = Q.help_tail q p head next;
      dequeue q p inner credits phi
    }
  }
}
