module Pulse.Lib.LogicalAtomicity.Example.MSQueue.Concurrent
#lang-pulse

(**
Shared-invariant clients and a verified two-producer/two-consumer harness.

Unlike Clients, workers do not privately own a known FIFO sequence. A shared
client invariant hides the model half at an existential current sequence.
Each worker constructs its own AU with Triple.from_invariant, and the commit
callback restores that model after the queue operation. Only shared handles,
node tickets, and result boxes cross task boundaries, not arbitrary AUs.

This demonstrates client-chosen ghost code and invariant-backed logical
atomicity under concurrent use. The payload interpretation here is emp;
exclusive payload transfer is demonstrated separately by Clients.fifo_ownership.
The worker callbacks deliberately return emp and discard sequence/result
relations. Consequently the harness proves safe sharing and preservation,
NOT a closed-world theorem that its two results permute [11;22] or that the
final queue is empty. runtime_test.ml checks those stronger observations.

consume may spin indefinitely; no fairness, termination, or lock-freedom
proof is supplied. Queue nodes are never reclaimed. Repeated native runs
should reuse the in-pool entry point because Task.teardown_pool currently
records logical completion without stopping its native worker threads.
*)

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module U32 = FStar.UInt32
module S = FStar.Seq
module N = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Storage
module Q = Pulse.Lib.LogicalAtomicity.Example.MSQueue.State
module E = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Enqueue
module R = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Dequeue
module T = Pulse.Lib.LogicalAtomicity.Triple
module Task = Pulse.Lib.Task
module C = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Clients

(** No additional client invariant state beyond the abstract model half. *)
let residual (_:S.seq U32.t) = emp
(** This harness sends plain values; it attaches no exclusive payload. *)
let resource (_:U32.t) = emp
(** Both the implementation handle and the client-model invariant handle.
The distinct-name condition is established separately when creating i. *)
let shared (#cells:N.arena) (q:Q.queue cells) (i:iname) =
  Q.is_queue q resource ** inv i (T.payload (Q.model q) residual)

(** Expose the definitional existential shape expected by the constructor;
this is reflexivity, not a new equivalence or abstract-state assumption. *)
let payload_equiv (#cells:N.arena) (q:Q.queue cells)
  : Lemma (T.payload (Q.model q) residual ==
      (exists* (xs:S.seq U32.t). Q.model q xs ** residual xs)) =
  assert (T.payload (Q.model q) residual ==
    (exists* (xs:S.seq U32.t). Q.model q xs ** residual xs))
    by (FStar.Tactics.V2.trefl ())

(** Both invariant bodies contain transferable resources for this emp payload. *)
instance send_shared (#cells:N.arena) (q:Q.queue cells) i : is_send (shared q i) =
  FStar.Tactics.Typeclasses.solve

(** Duplicate handles, not the model ownership inside their invariants. *)
instance dup_shared (#cells:N.arena) (q:Q.queue cells) i : duplicable (shared q i) =
  FStar.Tactics.Typeclasses.solve

(** Move private model ownership into a client invariant fresh relative to
the implementation invariant, ensuring later AU/queue openings are disjoint. *)
ghost fn share_model (#cells:N.arena) (q:Q.queue cells) (#xs:erased (S.seq U32.t))
  requires Q.is_queue q resource ** Q.model q xs
  returns i:iname
  ensures shared q i ** pure (not (i == q.Q.name))
{
  fold residual xs;
  fold T.payload (Q.model q) residual;
  let i = fresh_invariant (add_inv emp_inames q.Q.name) (T.payload (Q.model q) residual);
  fold shared q i;
  i
}

(** Locally construct a one-credit AU from a duplicated client handle.
At commit the callback installs the appended sequence in that invariant
and returns emp, leaving no private model half on the worker. *)
ghost fn prepare_enqueue (#cells:N.arena) (q:Q.queue cells) (i:iname) (n:N.id cells)
  preserves shared q i
  ensures E.update q n (add_inv emp_inames i) 1 (fun _ -> emp)
{
  unfold shared;
  dup_inv i (T.payload (Q.model q) residual);
  slprop_equivs ();
  // The sequence may differ from any earlier observation; beta is the
  // authority for choosing the replacement existential witness.
  ghost fn finish (xs:S.seq U32.t) (_:unit) ()
    requires emp ** residual xs ** E.beta q n xs ()
    ensures T.payload (Q.model q) residual ** emp
  {
    unfold residual;
    unfold E.beta;
    fold residual (S.append xs (S.create 1 (N.value cells n)));
    fold T.payload (Q.model q) residual;
  };
  payload_equiv q;
  T.from_invariant emp_inames i (Q.model q) residual (E.beta q n)
    (fun _ _ -> emp) emp finish;
  fold E.update q n (add_inv emp_inames i) 1 (fun _ -> emp);
  fold shared q i;
}

(** Construct the dequeue AU locally. Both result cases restore the client
invariant; intentionally discard the exact result/old-sequence relation,
which limits what the public consumer wrappers prove. *)
ghost fn prepare_dequeue (#cells:N.arena) (q:Q.queue cells) (i:iname)
  preserves shared q i
  ensures R.update q resource (add_inv emp_inames i) 1 (fun _ -> emp)
{
  unfold shared;
  dup_inv i (T.payload (Q.model q) residual);
  slprop_equivs ();
  // None keeps xs; Some uses the tail supplied by beta. P v is emp here.
  ghost fn finish (xs:S.seq U32.t) (result:option U32.t) ()
    requires emp ** residual xs ** R.beta q resource xs result
    ensures T.payload (Q.model q) residual ** emp
  {
    unfold residual;
    match result {
      None -> {
        rewrite R.beta q resource xs result as R.beta q resource xs None;
        unfold R.beta q resource xs None;
        fold residual xs;
        fold T.payload (Q.model q) residual;
      }
      Some v -> {
        rewrite R.beta q resource xs result as R.beta q resource xs (Some v);
        unfold R.beta q resource xs (Some v);
        with ys. _;
        unfold resource v;
        fold residual ys;
        fold T.payload (Q.model q) residual;
      }
    }
  };
  payload_equiv q;
  T.from_invariant emp_inames i (Q.model q) residual (R.beta q resource)
    (fun _ _ -> emp) emp finish;
  fold R.update q resource (add_inv emp_inames i) 1 (fun _ -> emp);
  fold shared q i;
}

(** Consume one fresh ticket and run the FIFO enqueue contract, preserving
shared handles. No generic sendability assertion about the constructed AU
is needed because preparation and use occur on the same worker. *)
divergent fn produce (#cells:N.arena) (q:Q.queue cells)
  (i:iname { not (i == q.Q.name) }) (n:N.id cells)
  preserves shared q i
  requires N.ticket cells n
{
  prepare_enqueue q i n;
  unfold shared;
  fold resource (N.value cells n);
  E.enqueue q resource n (add_inv emp_inames i) 1 (fun _ -> emp);
  fold shared q i;
}

(** Publish and commit while postponing final tail maintenance. The runtime
test pauses a producer here so another domain must help its published node. *)
divergent fn produce_deferred (#cells:N.arena) (q:Q.queue cells)
  (i:iname { not (i == q.Q.name) }) (n:N.id cells)
  preserves shared q i
  requires N.ticket cells n
  returns tail:N.id cells
  ensures Q.edge q tail n
{
  prepare_enqueue q i n;
  unfold shared;
  fold resource (N.value cells n);
  let tail = C.enqueue_deferred q resource n (add_inv emp_inames i) 1 (fun _ -> emp);
  fold shared q i;
  tail
}

(** Attempt only the postponed structural CAS; the enqueue already committed.
A false result is compatible with another producer having helped first. *)
fn finish_produce (#cells:N.arena) (q:Q.queue cells) (i:iname) (tail n:N.id cells)
  preserves shared q i
  requires Q.edge q tail n
  returns moved:bool
{
  unfold shared;
  let moved = Q.help_tail q resource tail n;
  fold shared q i;
  moved
}

(** One dequeue call, possibly returning None; internally it may retry CAS.
This wrapper exposes no value-specific postcondition beyond preserving shared. *)
divergent fn try_consume (#cells:N.arena) (q:Q.queue cells)
  (i:iname { not (i == q.Q.name) })
  preserves shared q i
  returns result:option U32.t
{
  prepare_dequeue q i;
  unfold shared;
  let result = R.dequeue q resource (add_inv emp_inames i) 1 (fun _ -> emp);
  fold shared q i;
  result
}

(** Retry empty results until some value is returned. Availability and fair
scheduling are not assumed or proven, hence the divergent specification. *)
divergent fn rec consume (#cells:N.arena) (q:Q.queue cells)
  (i:iname { not (i == q.Q.name) })
  preserves shared q i
  returns value:U32.t
{
  let result = try_consume q i;
  match result {
    None -> { consume q i }
    Some value -> { value }
  }
}

(** Owned result slot after a consumer; its value is intentionally hidden. *)
let output (r:B.box U32.t) = exists* v. B.pts_to r v

(** Retain the queue and arena for further runtime observations after joins.
The ghost client-invariant name is erased; values are not refined to a
permutation by this type or the harness postcondition. *)
noeq type run_result = {
  cells:N.arena;
  queue:Q.queue cells;
  model_inv:iname;
  values:(U32.t & U32.t);
}

(** Spawn two consumers and producers with disjoint tickets/result boxes,
join all tasks, free result boxes, and return shared queue access. Preserve
the supplied pool for reuse. The postcondition is intentionally weaker
than the permutation and final-emptiness assertions in runtime_test.ml. *)
divergent fn two_producers_two_consumers_in_pool (pool:Task.pool)
  preserves Task.pool_alive pool
  returns result:run_result
  ensures shared result.queue result.model_inv
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
  let q = Q.create cells resource;
  let i = share_model q;
  let a = B.alloc 0ul;
  let b = B.alloc 0ul;
  dup (shared q i) ();
  let c1 = Task.spawn pool #_ #(shared q i ** B.pts_to a 0ul) #(shared q i ** output a)
    fn _ {
      let v = consume q i;
      B.(a := v);
      fold output a;
    };
  dup (shared q i) ();
  let c2 = Task.spawn pool #_ #(shared q i ** B.pts_to b 0ul) #(shared q i ** output b)
    fn _ {
      let v = consume q i;
      B.(b := v);
      fold output b;
    };
  dup (shared q i) ();
  let p1 = Task.spawn pool #_ #(shared q i ** N.ticket cells 1ul) #(shared q i)
    fn _ { produce q i 1ul };
  dup (shared q i) ();
  let p2 = Task.spawn pool #_ #(shared q i ** N.ticket cells 2ul) #(shared q i)
    fn _ { produce q i 2ul };
  Task.await p1;
  Task.await p2;
  Task.await c1;
  Task.await c2;
  unfold output a;
  unfold output b;
  with bv. _;
  let av = B.(!a);
  let bv = B.(!b);
  B.free a;
  B.free b;
  let result = { cells; queue=q; model_inv=i; values=(av, bv) };
  rewrite each cells as result.cells;
  rewrite each q as result.queue;
  rewrite each i as result.model_inv;
  result
}

(** Single-run convenience wrapper allocating four workers. Logical teardown
does not currently stop native workers, so do not allocate one pool per
iteration in an unbounded or long-running test process. *)
divergent fn two_producers_two_consumers ()
  returns result:run_result
  ensures shared result.queue result.model_inv
{
  let pool = Task.setup_pool 4;
  let result = two_producers_two_consumers_in_pool pool;
  Task.teardown_pool pool;
  drop_ (Task.pool_done pool);
  result
}
