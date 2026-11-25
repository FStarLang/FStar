# A logically atomic lock-coupling set

This example revisits Section 8 of Bart Jacobs and Frank Piessens,
[*Expressive Modular Fine-Grained Concurrency Specification*](https://people.cs.kuleuven.be/~bart.jacobs/popl2011.pdf),
POPL 2011. It implements a sorted, hand-over-hand locked linked-list set and
proves the paper's producer/consumer property: **after a successful removal,
a second removal of that key fails even if the producer runs between calls**.

The implementation is a verified library client, with no checker changes,
new primitive axioms, or prophecies. It uses the
[logical-atomicity foundations](../../../../../lib/pulse/logical_atomicity/README.md).
See the [parent guide](../README.md) for the other examples.

## Reading order

1. **[Operations.fsti](Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Operations.fsti)**:
   the public AU contract. Read `alpha`, `beta`, `update`, then the three operations.
2. **[Clients](Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Clients.fst)**:
   specialize those contracts to private model ownership. `sequential` proves
   exact results for insertion, duplicate insertion, membership, missing removal,
   middle/head/tail removal, and reinsertion; its final model is empty.
3. **[Protocol](Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Protocol.fst)**:
   the client's exact partition of produced keys into present and removed keys.
   `cannot_remove_twice` and `drained` are the central pure theorems.
4. **[Concurrent](Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Concurrent.fst)**:
   `prepare_add`, `prepare_remove`, and `prepare_absent` build AUs from the
   client invariant. `consume_twice` mirrors the paper's conditional assertion;
   `remove_again` exposes its exact false-result postcondition.
   Then read `run_in_pool`, `finished`, `empty_at_open`, and `certify_empty`.
5. **[Model](Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Model.fst)**,
   **[Storage](Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Storage.fst)**,
   **[State](Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.State.fst)**,
   **[Operations.fst](Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Operations.fst)**:
   follow the implementation proof from set membership and adjacent-node gaps
   through shadow ownership, lock coupling, and AU commitment.
6. **[Shared](Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Shared.fst)**:
   a different client invariant permits arbitrary concurrent add/remove/contains,
   without the once-only producer restriction.
7. **[Rejections](Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Rejections.fst)**
   and **[runtime_test.ml](runtime_test.ml)**: distinguish rejected misuse,
   mechanized client guarantees, and native execution checks.

## Scope relative to the paper

| Paper, Section 8 | This example |
| --- | --- |
| Dynamically allocated integer-key nodes, with negative/positive infinity sentinels | A fixed universe `1..capacity`, with node indices `0` and `capacity+1` as sentinels |
| Sorted linked list, hand-over-hand semaphore acquisition | Sorted linked list, one existing `Pulse.Lib.SpinLock` per node |
| Fresh allocation on insertion; removed nodes are not reclaimed | Preallocate all nodes; acquire an inactive node's lock for insertion; removal clears its link and releases it for reuse |
| `oldNext` fields and a ghost membership bag | Fractional ghost shadow links in a total registry of all slots |
| Client-supplied success/failure ghost closures | A uniform logically atomic `alpha`/`beta` transition and a client-chosen AU continuation |
| Producer cursor and last removed key | Producer cursor and the entire removed-key set, enabling an exact final-emptiness theorem |

The bounded universe is a deliberate representation change, **not** a proof
of the paper's dynamically allocated unbounded set. It imposes no lifetime
limit on operations: ordinary set clients can remove and reinsert a key
arbitrarily often. Only the *paper client protocol* forbids reinsertion.

The paper also discusses MCAS/RDCSS; those algorithms are not implemented here.
Its earlier parallel-increment example is not duplicated in this directory.

## Public contract

For the abstract membership set `S` observed at commitment:

| Operation | Result | New model |
| --- | --- | --- |
| `add k` | `k` was absent from `S` | `S` with `k` present |
| `remove k` | `k` was present in `S` | `S` with `k` absent |
| `contains k` | `k` was present in `S` | `S`, unchanged |

`Model` represents this finite mathematical set by a ghost characteristic
sequence. **The runtime implementation is a linked list, not a bit set.**
The transition changes no other membership. The AU quantifies over the state
at commitment, not a snapshot taken on entry; a `phi` continuation can keep
client-private ownership and relate the result to client ghost state.

The operation's client-open mask must exclude the implementation invariant.
Each operation buys the AU's opening credits and one implementation-invariant
credit. Traversal also explicitly funds its invariant observations.
As with the other examples, `run_closed` exposes an `all_inames` footprint,
so operations cannot run inside an already-open lexical invariant.

## Implementation and linearization

Each node owns an immutable lock handle and a boxed mutable next index.
Its lock protects the physical next field and half of a ghost shadow.
The implementation invariant owns the other half of every shadow and half
of the abstract model. The client owns the remaining model half.
Inactive nodes have shadow and physical next index zero.

Holding one shadow half freezes that node's abstract outgoing edge.
`State.advance` acquires the successor before releasing the predecessor;
agreement against the current registry then proves that the successor is
still live. This is why retirement/reuse is safe without optimistic stale
pointer observations, an ABA argument, or prophecies.

An insertion into a missing-key gap locks the reusable target, initializes
its next field, and links it from the predecessor. A successful removal locks
the target, reads its successor, clears its next field, and bypasses it.
Both locks remain held throughout those writes and the model update.

**The AU commits at a ghost linearization point after preparation and before
unlocking.** For a nonchanging operation it commits while the observed
predecessor edge is still locked. No other thread can observe an intermediate
physical edge. The proof does not label multiple physical writes as one
atomic instruction, and it adds no generic atomic-pointer primitive.

The implementation invariant is entirely ghost state: there is **no global
runtime set lock**. The generic
[`MSQueue.Actions`](../msqueue/Pulse.Lib.LogicalAtomicity.Example.MSQueue.Actions.fst)
helpers are reused for AU composition and delayed closing; they do not
depend on the FIFO implementation. The lexical implementation invariant is
closed before the suspended client closing update runs.

## Client guarantees

The producer owns half of a ghost cursor `p`, and the consumer owns half of
a ghost removed-key set `D`. Their invariant stores the other halves and says:

```text
0 <= p <= capacity
D is a subset of {1,...,p}
S = {1,...,p} \ D
```

The producer's next call inserts `p+1` and is proved successful. A successful
consumer removal adds its key to `D`; a failed removal leaves `D` unchanged.
Thus successful removal gives stable absence despite later producer steps,
whereas failed removal does **not** rule out a future insertion.

`consume_twice` proves the paper's assertion for an arbitrary key.
`run_in_pool` spawns actual producer and consumer tasks, checks a second
removal at every consumed key, joins both, and returns `finished` ownership
with a proved-false violation flag. `finished` records the full produced and
removed prefixes. `empty_at_open` proves that the **actual model borrowed
from the client invariant** is then exactly empty; `certify_empty` applies
that theorem after joining. Model ownership stays inside the permanent
invariant, rather than being unsoundly extracted from it.

This is more than a resource-safety-only concurrent client. In contrast,
`Shared.perform` deliberately returns an unconstrained boolean while retaining
the shared model invariant; its richer transition is supplied by the operation
AU, and its concrete histories are additionally checked by the native harness.

The paper's ghost-closure idea is a predecessor of the client ghost-code
style used in HoCAP. Here `Triple.from_invariant` packages that client code
in the Iris-inspired AU protocol. TaDA supplies a related abstract-atomic
view of operations; no translation or equivalence to those logics is claimed.
The set needs locking, not helping; see the sibling `Helping` example for
another thread committing a caller's continuation.

## Build and validation

From the repository root, with the stage-3 compiler already built:

```sh
opam exec --switch=5.3.0 -- \
  make -C pulse/share/pulse/examples/logical_atomicity/concurrent_set -j$(nproc)
```

`verify` checks the F*/Pulse modules, including expected failures;
`runtime-test` also extracts, compiles, and executes the native tests.
Both are integrated into the parent logical-atomicity example targets.
Artifacts live in `pulse/build/logical_atomicity/concurrent_set/`.
The local editor configuration selects the same stage-3 compiler.

Native coverage includes sequential exact-result checks, forced producer
interference between removals, insertion before a locked successor,
four-way same-key insertion/removal races with node reuse, 64 small histories,
and 32 runs of the verified producer/consumer task client.
Each history contains nine racing operations plus three final membership
observations; a backtracking checker respects all recorded real-time edges.
Negative controls ensure the checker rejects impossible histories.

The negative F* tests reject advancing after unlocking the predecessor,
repeating a producer insertion, and treating a failed removal as a tombstone.

## Boundaries and limitations

Partial correctness only: no scheduler fairness, termination, starvation
freedom, or lock-freedom theorem. The runtime uses the existing mutex-backed
spin-lock realization; this is not a weak-memory or lock-free experiment.
The native driver and history checker are handwritten and must respect
erased key/ownership preconditions. Checking finitely many histories is
not an exhaustive concurrency proof.

All nodes are preallocated and retained. There is no set destructor, dynamic
allocation/reclamation proof, or owned payload resource per key.
Arena lookup is immutable-list indexing, not constant-time addressing;
this is a proof example, not a performance implementation.
Repeated native task runs reuse one pool because the existing task library's
logical teardown does not stop its native worker domains.
