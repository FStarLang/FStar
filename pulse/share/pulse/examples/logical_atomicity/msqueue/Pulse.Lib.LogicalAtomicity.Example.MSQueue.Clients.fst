module Pulse.Lib.LogicalAtomicity.Example.MSQueue.Clients
#lang-pulse

(**
Sequential clients demonstrating usable FIFO and ownership specifications.

Start here to see what the queue's logical-atomic contracts buy a caller.
Actions.from_owned turns private model ownership into a zero-credit AU;
the same concurrent implementation then yields ordinary sequential Hoare
specifications. No queue implementation details are needed to prove which
value pop returns or to regain an exclusive payload.

`fifo_ownership` proves exact results and frees transferred payload boxes.
`enqueue_deferred` exposes the interval between publication and final tail
maintenance; delayed_tail and stale_tail_retry exercise helping/retry paths.
Those latter clients prove an empty final model but do NOT state that their
returned diagnostic booleans are true; runtime_test.ml checks that behavior.

All nodes are one-use arena entries and remain owned by the queue invariant
after draining. Payload reclamation here is not queue-node reclamation.
These are partial-correctness examples; no progress theorem is inferred
from their ordinary sequential-looking specifications.
*)

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module U32 = FStar.UInt32
module S = FStar.Seq
module N = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Storage
module Q = Pulse.Lib.LogicalAtomicity.Example.MSQueue.State
module D = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Actions
module E = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Enqueue
module R = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Dequeue
module A = Pulse.Lib.LogicalAtomicity.Atomic

(** Derive ordinary FIFO append from the AU contract when the caller
privately owns the client model half. Consume a ticket and P(value n). *)
divergent fn enqueue_owned (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop)
  (n:N.id cells) (#xs:erased (S.seq U32.t))
  preserves Q.is_queue q p
  requires Q.model q xs ** N.ticket cells n ** p (N.value cells n)
  ensures Q.model q (S.append xs (S.create 1 (N.value cells n)))
{
  D.from_owned (Q.model q) (E.beta q n) xs;
  rewrite A.atomic_update emp_inames emp_inames 0 (Q.model q) (E.beta q n)
    (fun _ y -> E.beta q n xs y) as E.update q n emp_inames 0 (E.beta q n xs);
  E.enqueue q p n emp_inames 0 (E.beta q n xs);
  unfold E.beta q n xs ();
}

(** Specialize dequeue's client continuation to return its entire beta,
preserving all abstract-state and payload facts for the caller. *)
divergent fn dequeue_owned (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop)
  (#xs:erased (S.seq U32.t))
  preserves Q.is_queue q p
  requires Q.model q xs
  returns result:option U32.t
  ensures R.beta q p xs result
{
  D.from_owned (Q.model q) (R.beta q p) xs;
  fold R.update q p emp_inames 0 (R.beta q p xs);
  R.dequeue q p emp_inames 0 (R.beta q p xs)
}

(** A known nonempty private model rules out None and identifies the exact
returned first value and remaining tail; P v is recovered for client use. *)
divergent fn pop_owned (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop)
  (#v:erased U32.t) (#xs:erased (S.seq U32.t))
  preserves Q.is_queue q p
  requires Q.model q (S.cons #U32.t v xs)
  returns result:U32.t
  ensures Q.model q xs ** p v ** pure (result == v)
{
  let result = dequeue_owned q p;
  match result {
    None -> {
      rewrite R.beta q p (S.cons #U32.t v xs) result as R.beta q p (S.cons #U32.t v xs) None;
      unfold R.beta q p (S.cons #U32.t v xs) None;
      unreachable ()
    }
    Some value -> {
      rewrite R.beta q p (S.cons #U32.t v xs) result as R.beta q p (S.cons #U32.t v xs) (Some value);
      unfold R.beta q p (S.cons #U32.t v xs) (Some value);
      with ys. _;
      S.lemma_cons_inj #U32.t v value xs ys;
      rewrite Q.model q ys as Q.model q xs;
      rewrite p value as p v;
      value
    }
  }
}

(** A known empty private model rules out Some and remains unchanged. *)
divergent fn empty_owned (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop)
  preserves Q.is_queue q p ** Q.model q S.empty
  returns result:option U32.t
  ensures pure (result == None)
{
  let result = dequeue_owned q p;
  match result {
    None -> {
      rewrite R.beta q p S.empty result as R.beta q p S.empty None;
      unfold R.beta q p S.empty None;
      None
    }
    Some value -> {
      rewrite R.beta q p S.empty result as R.beta q p S.empty (Some value);
      unfold R.beta q p S.empty (Some value);
      with ys. _;
      unreachable ()
    }
  }
}

(** Value tags 11/22 designate exclusive external boxes containing 101/202.
This intentionally distinguishes a queue's numeric value from its resource. *)
let payload (a b:B.box U32.t) (v:U32.t) =
  if v = 11ul then B.pts_to a 101ul
  else if v = 22ul then B.pts_to b 202ul
  else emp

(** Prove empty, append 11 then 22 with exclusive boxes, pop in that order,
read/free both recovered boxes, and prove empty again. The exact returned
pair (101,202) demonstrates functional correctness and ownership recovery. *)
divergent fn fifo_ownership ()
  returns values:(U32.t & U32.t)
  ensures exists* (cells:N.arena) (q:Q.queue cells) a b.
    Q.is_queue q (payload a b) ** Q.model q S.empty **
    pure (values == (101ul, 202ul))
{
  let dummy = B.alloc N.null;
  let first = B.alloc N.null;
  let second = B.alloc N.null;
  let cells:N.arena = [
    { N.next=dummy; N.value=0ul };
    { N.next=first; N.value=11ul };
    { N.next=second; N.value=22ul }
  ];
  rewrite B.pts_to dummy N.null as N.ticket cells 0ul;
  rewrite B.pts_to first N.null as N.ticket cells 1ul;
  rewrite B.pts_to second N.null as N.ticket cells 2ul;
  let a = B.alloc 101ul;
  let b = B.alloc 202ul;
  let q = Q.create cells (payload a b);
  let _ = empty_owned q (payload a b);
  rewrite B.pts_to a 101ul as payload a b (N.value cells 1ul);
  enqueue_owned q (payload a b) 1ul;
  rewrite B.pts_to b 202ul as payload a b (N.value cells 2ul);
  enqueue_owned q (payload a b) 2ul;
  S.append_empty_l (S.create 1 11ul);
  S.append_empty_r (S.create 1 22ul);
  rewrite each (N.value cells 1ul) as 11ul;
  rewrite each (N.value cells 2ul) as 22ul;
  rewrite Q.model q (S.append (S.append S.empty (S.create 1 11ul)) (S.create 1 22ul))
    as Q.model q (S.cons 11ul (S.cons 22ul S.empty));
  let x = pop_owned q (payload a b) #11ul #(S.cons 22ul S.empty);
  rewrite payload a b 11ul as B.pts_to a 101ul;
  let y = pop_owned q (payload a b) #22ul #S.empty;
  rewrite payload a b 22ul as B.pts_to b 202ul;
  let av = B.(!a);
  let bv = B.(!b);
  B.free a;
  B.free b;
  let _ = empty_owned q (payload a b);
  (av, bv)
}

(** Enqueue through its successful link/commit but defer the final tail CAS.
Returning phi means enqueue has already linearized; the returned edge lets
this thread attempt maintenance later even if another producer helps first.
Client masks/credits remain general for use by the concurrent test client. *)
divergent fn rec enqueue_deferred (#cells:N.arena) (q:Q.queue cells) (p:U32.t -> slprop)
  (n:N.id cells) (inner:inames { not (mem_inv inner q.Q.name) }) (credits:nat) (phi:unit -> slprop)
  preserves Q.is_queue q p
  requires E.update q n inner credits phi ** N.ticket cells n ** p (N.value cells n)
  returns tail:N.id cells
  ensures phi () ** Q.edge q tail n
{
  let tail = Q.read_pointer q p false;
  let next = Q.read_successor q p tail;
  if (next = N.null) {
    rewrite (if next == N.null then Q.observed q false tail else Q.edge q tail next)
      as Q.observed q false tail;
    let ok = E.try_link q p tail n inner credits phi;
    unfold E.attempt_post q p tail n inner credits phi ok;
    if ok { tail }
    else { enqueue_deferred q p n inner credits phi }
  } else {
    rewrite (if next == N.null then Q.observed q false tail else Q.edge q tail next)
      as Q.edge q tail next;
    let _ = Q.help_tail q p tail next;
    enqueue_deferred q p n inner credits phi
  }
}

(** Publish the first node with tail maintenance delayed; enqueue the second,
which can help the first, then attempt the stale final CAS and drain FIFO.
The postcondition proves final emptiness, not the diagnostic bool's value. *)
divergent fn delayed_tail ()
  returns helped:bool
  ensures exists* (cells:N.arena) (q:Q.queue cells).
    Q.is_queue q (fun _ -> emp) ** Q.model q S.empty
{
  let dummy = B.alloc N.null;
  let first = B.alloc N.null;
  let second = B.alloc N.null;
  let cells:N.arena = [
    { N.next=dummy; N.value=0ul };
    { N.next=first; N.value=11ul };
    { N.next=second; N.value=22ul }
  ];
  rewrite B.pts_to dummy N.null as N.ticket cells 0ul;
  rewrite B.pts_to first N.null as N.ticket cells 1ul;
  rewrite B.pts_to second N.null as N.ticket cells 2ul;
  let q = Q.create cells (fun _ -> emp);
  D.from_owned (Q.model q) (E.beta q 1ul) S.empty;
  rewrite A.atomic_update emp_inames emp_inames 0 (Q.model q) (E.beta q 1ul)
    (fun _ y -> E.beta q 1ul S.empty y) as E.update q 1ul emp_inames 0 (E.beta q 1ul S.empty);
  let old_tail = enqueue_deferred q (fun _ -> emp) 1ul emp_inames 0 (E.beta q 1ul S.empty);
  unfold E.beta q 1ul S.empty ();
  enqueue_owned q (fun _ -> emp) 2ul;
  let moved = Q.help_tail q (fun _ -> emp) old_tail 1ul;
  S.append_empty_l (S.create 1 11ul);
  S.append_empty_r (S.create 1 22ul);
  rewrite each (N.value cells 1ul) as 11ul;
  rewrite each (N.value cells 2ul) as 22ul;
  rewrite Q.model q (S.append (S.append S.empty (S.create 1 11ul)) (S.create 1 22ul))
    as Q.model q (S.cons 11ul (S.cons 22ul S.empty));
  let _ = pop_owned q (fun _ -> emp) #11ul #(S.cons 22ul S.empty);
  let _ = pop_owned q (fun _ -> emp) #22ul #S.empty;
  not moved
}

(** Keep an old tail observation across another enqueue, attempt linking
through it, and retry with restored ticket/payload if it fails. Both paths
must establish the same FIFO model before draining; the returned retry flag
is an executable regression observation, not an asserted pure theorem here. *)
divergent fn stale_tail_retry ()
  returns retried:bool
  ensures exists* (cells:N.arena) (q:Q.queue cells).
    Q.is_queue q (fun _ -> emp) ** Q.model q S.empty
{
  let dummy = B.alloc N.null;
  let first = B.alloc N.null;
  let second = B.alloc N.null;
  let cells:N.arena = [
    { N.next=dummy; N.value=0ul };
    { N.next=first; N.value=11ul };
    { N.next=second; N.value=22ul }
  ];
  rewrite B.pts_to dummy N.null as N.ticket cells 0ul;
  rewrite B.pts_to first N.null as N.ticket cells 1ul;
  rewrite B.pts_to second N.null as N.ticket cells 2ul;
  let q = Q.create cells (fun _ -> emp);
  let stale = Q.read_pointer q (fun _ -> emp) false;
  enqueue_owned q (fun _ -> emp) 1ul;
  let xs:erased (S.seq U32.t) = hide (S.append S.empty (S.create 1 (N.value cells 1ul)));
  rewrite Q.model q (S.append S.empty (S.create 1 (N.value cells 1ul))) as Q.model q xs;
  D.from_owned (Q.model q) (E.beta q 2ul) xs;
  rewrite A.atomic_update emp_inames emp_inames 0 (Q.model q) (E.beta q 2ul)
    (fun _ y -> E.beta q 2ul xs y) as E.update q 2ul emp_inames 0 (E.beta q 2ul xs);
  let ok = E.try_link q (fun _ -> emp) stale 2ul emp_inames 0 (E.beta q 2ul xs);
  unfold E.attempt_post q (fun _ -> emp) stale 2ul emp_inames 0 (E.beta q 2ul xs) ok;
  if ok {
    let _ = Q.help_tail q (fun _ -> emp) stale 2ul;
  } else {
    E.enqueue q (fun _ -> emp) 2ul emp_inames 0 (E.beta q 2ul xs);
  };
  unfold E.beta q 2ul xs ();
  S.append_empty_l (S.create 1 11ul);
  S.append_empty_r (S.create 1 22ul);
  rewrite Q.model q (S.append xs (S.create 1 (N.value cells 2ul)))
    as Q.model q (S.cons 11ul (S.cons 22ul S.empty));
  let _ = pop_owned q (fun _ -> emp) #11ul #(S.cons 22ul S.empty);
  let _ = pop_owned q (fun _ -> emp) #22ul #S.empty;
  not ok
}
