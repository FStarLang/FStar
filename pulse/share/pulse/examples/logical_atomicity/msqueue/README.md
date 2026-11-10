# Michael--Scott FIFO queue

This example exercises the library-only logical-atomicity API on a
Michael--Scott-style queue: exact FIFO sequence transitions, exclusive
payload transfer, retrying CAS operations, and structural tail helping.
No checker changes, pointer-atomic axioms, or prophecies are added.

See the [parent examples guide](../README.md) for the progression from small
examples to this queue, and the
[library guide](../../../../../lib/pulse/logical_atomicity/README.md) for the
alpha/beta/phi protocol, masks, and connections to Iris, TaDA, and HoCAP.
All module names here have the prefix
`Pulse.Lib.LogicalAtomicity.Example.MSQueue`.

## Reading order

1. **[Clients](Pulse.Lib.LogicalAtomicity.Example.MSQueue.Clients.fst)**:
   begin with `enqueue_owned`, `dequeue_owned`, `pop_owned`, and `empty_owned`,
   then `fifo_ownership`. Private model ownership specializes the concurrent
   AU contracts to ordinary sequential FIFO reasoning. The last client
   transfers two exclusive boxed payloads through the queue, retrieves them
   in order, and frees them.
2. **[The implementation proof](#implementation-proof-reading-order)**:
   follow the dependency order below, from the pure history model through
   physical ownership to enqueue/dequeue linearization. Then return to
   `Clients.enqueue_deferred`, `delayed_tail`, and `stale_tail_retry` for
   clients that expose publication, helping, and failed-CAS scheduling points.
3. **[Concurrent](Pulse.Lib.LogicalAtomicity.Example.MSQueue.Concurrent.fst)**:
   read `share_model`, `prepare_enqueue`, and `prepare_dequeue`, then the
   producer/consumer wrappers and `two_producers_two_consumers_in_pool`.
   Workers construct AUs from a shared client invariant using
   `Triple.from_invariant`, rather than sending arbitrary updates between
   threads. The operation contracts are stronger than this harness's final
   postcondition; see [the client-specification gaps](#client-guarantees-and-gaps).
4. **[Rejections](Pulse.Lib.LogicalAtomicity.Example.MSQueue.Rejections.fst)**
   and **[runtime_test.ml](runtime_test.ml)**: the rejection cases prohibit
   reusing an enqueue ticket and reading a transferred payload before
   ownership is returned. Finish with the atomic realizations below to
   distinguish verified contracts from handwritten backend assumptions.

## Representation and abstract contract

The queue uses an immutable arena of cells and UInt32 node IDs because Pulse's
existing atomic primitives are UInt32-based. Each cell has an immutable value
and an atomic next field. ID `0xffffffff` is null; node zero is the initial
dummy. Enqueue consumes a **one-use node ticket**, backed by exclusive ownership
of that node's next field, and an associated payload resource `P value`.

The logical-atomic specifications describe a sequence, not just a count or bag:

* Enqueue changes `xs` to `xs ++ [value]` and transfers `P value` into the queue.
* Successful dequeue changes `value :: xs` to `xs` and returns `P value`.
* Empty dequeue proves that the abstract sequence was empty at its
  linearization point, not necessarily when the operation returns.

Physical links remain owned by the queue even after their payloads have been
dequeued. Nodes are neither reclaimed nor reused. This gives a finite lifetime
allocation budget, not an unbounded allocator or a recycling bounded queue.
Arena lookup is list indexing; this is not a constant-time storage backend.
Unlike the sibling [concurrent set](../concurrent_set/README.md), this queue
cannot reuse a node after removing its payload.

## Implementation proof reading order

Read the operation contracts in `Clients` first, then follow this dependency
order to understand why the implementation satisfies them:

| Order | Module | Main proof obligation |
| --- | --- | --- |
| 1 | [Model](Pulse.Lib.LogicalAtomicity.Example.MSQueue.Model.fst) | Pure append-only history, monotone head/tail indices, and correspondence between physical transitions and FIFO sequence operations. |
| 2 | [Storage](Pulse.Lib.LogicalAtomicity.Example.MSQueue.Storage.fst) | Focus/restore physical links, consume exclusive node tickets, prove freshness from ownership, and collect live payload resources. |
| 3 | [Atomics interface](Pulse.Lib.LogicalAtomicity.Example.MSQueue.Atomics.fsti) | Exact load and weak-CAS contracts supplied by existing Pulse primitives; failure need not imply a value mismatch. |
| 4 | [State](Pulse.Lib.LogicalAtomicity.Example.MSQueue.State.fst) | Connect physical pointers and links, authoritative history, payload ownership, and a client model half-reference; justify stale observations and tail helping. |
| 5 | [Actions](Pulse.Lib.LogicalAtomicity.Example.MSQueue.Actions.fst) | Compose an open client AU with one implementation step, and defer its closing action until the implementation invariant is restored. |
| 6 | [Enqueue](Pulse.Lib.LogicalAtomicity.Example.MSQueue.Enqueue.fst) | Transfer the fresh node and payload at successful link CAS; restore all untransferred ownership on failure. |
| 7 | [Dequeue](Pulse.Lib.LogicalAtomicity.Example.MSQueue.Dequeue.fst) | Prove empty results at a null-next read and exact FIFO removal with payload return at successful head CAS. |

The history authority and persistent snapshots play a role analogous to
authoritative ghost state with persistent observations in Iris, using Pulse's
existing ghost-reference APIs. Prefix stability and unique node identities
justify stale observations without ABA or prophecies. Snapshot ownership does
not assert that a pointer remains current; successful CAS supplies that fact.

`Actions` is generic despite its queue namespace: the concurrent-set example
also imports its AU-composition helpers, without depending on the FIFO model
or implementation.

## Linearization, masks, and helping

Enqueue commits at the successful link CAS. Nonempty dequeue commits at the
successful head CAS, and empty dequeue commits at a null-next read. Dequeue
reads head, next, then tail; the snapshot proof justifies this ordering and
avoids a second head-validation load.

Tail CAS operations help structural progress but do not change the abstract
sequence or commit another operation's client continuation. This differs from
the sibling [Helping](../Pulse.Lib.LogicalAtomicity.Example.Helping.fst)
descriptor example, where another thread constructs and commits the caller's
AU. Here, enqueue has already committed before its final tail maintenance
can be helped.

`Actions` keeps the client's opening explicit while the implementation
invariant opens and closes lexically around one physical step. The closing
update runs only after that implementation invariant has been restored. The
client's open mask must exclude the queue invariant. Failed attempts restore
the AU and any untransferred ownership, but do not refund spent credits.
Executable attempts use `run_closed` and expose `all_inames`, so they cannot
be called inside an already-open lexical invariant.

## Client guarantees and gaps

`fifo_ownership` proves exact FIFO results, recovers exclusive boxes containing
101 and 202, frees them, and proves the final queue empty. `delayed_tail` exposes
the scheduling point after linking; `stale_tail_retry` exercises a stale link
CAS. These latter clients prove their final empty models, but do not refine
their diagnostic booleans to `true`; the runtime tests check those booleans.

The concurrent client establishes safe sharing and uses the FIFO operation
contracts. Each worker constructs its own AU from sendable resources; no
arbitrary-update sendability is assumed. Its payload interpretation is `emp`,
so exclusive payload transfer is demonstrated separately by `fifo_ownership`.
Its callbacks deliberately discard the old-sequence/result relation:
the harness does **not** additionally prove a closed-world permutation theorem
for its two returned values or final emptiness. Runtime tests check those
properties for the executions tested. These are client-specification gaps,
not gaps in the sequence-based enqueue/dequeue contracts.

## Build and editor support

From the repository root, with the stage-3 compiler already built:

```sh
opam exec --switch=5.3.0 -- \
  make -C pulse/share/pulse/examples/logical_atomicity/msqueue -j$(nproc)
```

`verify` checks the F*/Pulse modules, including both atomic wrappers and the
expected failures. `runtime-test` depends on those proofs, extracts the clients,
and compiles/runs the native regressions. `all` runs both; the parent
logical-atomicity example targets also include this directory.
Artifacts stay in `pulse/build/logical_atomicity/msqueue/`.

The local [editor configuration](Pulse.fst.config.json) selects the stage-3
compiler and source/core include paths. The [Makefile](Makefile) uses core
includes for verification only: extraction selects installed/native
realizations rather than core semantic implementations. Neither configuration
enables admits.

## Executable validation and trust boundary

[`runtime_test.ml`](runtime_test.ml) covers FIFO payload recovery, stale and
deliberately failed CAS attempts, delayed tail helping, a producer paused after
linking while another producer helps, 64 two-producer/two-consumer runs, and
16 native four-producer/four-consumer batches of 64 distinct payloads each.

The repeated verified clients reuse one task pool:
`Task.teardown_pool` currently establishes logical completion but does not
stop its worker threads. Native stress-test domains are explicitly joined.

The runtime reuses the native lock, fork, and sleep realizations from the
existing task-pool tests. For queue atomics, read these files together:

* [Atomics-model.fst](Pulse.Lib.LogicalAtomicity.Example.MSQueue.Atomics-model.fst)
  verifies the wrapper against existing Pulse primitive contracts.
* [Atomics-ocaml.fst](Pulse.Lib.LogicalAtomicity.Example.MSQueue.Atomics-ocaml.fst)
  has verified bodies but selects handwritten externals for extraction.
* [MSQueue_atomics.ml](MSQueue_atomics.ml) implements those externals with
  a mutex around each load/CAS, not an entire queue operation, and injects
  permitted spurious CAS failures.

This backend tests concurrent safety, **not lock-free execution**. The
handwritten target realization remains a runtime trust boundary; verifying
the F* wrapper does not prove the OCaml code correct.

The handwritten OCaml harness is also not verified. It must respect erased
preconditions such as one-use tickets and disjoint producer IDs. Sorted-result
comparisons check loss/duplication for executed schedules, not every concurrent
FIFO history or all possible schedules. The F* operation proofs, not the stress
tests, establish the abstract sequence transitions.

## Scope and limitations

Partial correctness only: no fairness, termination, starvation-freedom, or
lock-freedom theorem. Contention or spurious CAS failures can prevent return.
There is no destructor, node reclamation, node reuse, or ABA treatment.
Recovering and freeing a payload is not reclaiming its queue node.
Weak-memory atomics and native lock-free backends are outside this validation.
There are no prophecy variables or retrospective-commit rules; the intended
Herlihy--Wing FIFO example remains deferred rather than weakened to a bag
specification.
