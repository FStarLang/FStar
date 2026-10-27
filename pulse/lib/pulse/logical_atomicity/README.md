# Logical atomicity

This is a library-only prototype: no Pulse syntax, elaboration, or checker
changes. The semantic model and all combinators are verified; there are no new
axioms or admitted proofs.

Foundations live in this directory; executable and rejection examples live in
[`pulse/share/pulse/examples/logical_atomicity`](../../../share/pulse/examples/logical_atomicity).
The example module names retain `Pulse.Lib.LogicalAtomicity.Example` for source
compatibility, but they are no longer roots of the Pulse library build or
included through its `fstar.include`. Each source has a module-level account
of its proof role and limitations, followed by definition-level contracts
and proof explanations.

## Layers

* `Masks`: actions with distinct initial/final masks, composition, framing, and
  conversion to ordinary Pulse atomic computations. Its `-model.fst` proves the
  operations against Pulse's existing semantics. Extraction annotations erase
  the model and ghost actions, retaining ordinary sequencing and atomic calls.
* `Invariant`: separate opening and closing of existing `Pulse.Lib.Inv`
  invariants, preserving locality and later-credit requirements.
* `Update`: resource-capturing, first-class mask-changing `wand` and `fupd`,
  with introduction, elimination, composition, framing, and mapping.
* `Atomic`: accessors and atomic updates. An accessor exposes `alpha x` and
  an **additive** choice between abort and commit, not two independently
  consumable continuations. Abort restores the update; commit consumes it and
  transforms `beta x y` into the client postcondition `phi x y`.
* `Triple`: builds an atomic update from a client invariant
  `exists* x. alpha x ** residual x`, captured ownership, and a ghost
  continuation that reestablishes the invariant at the linearization point.

An atomic update hides a resource state and a reusable pure step witness.
Each step opens an accessor whose abort restores that state. This existential
coinduction encoding supports arbitrarily many retries without a recursive
spatial predicate.

### Reading the contracts

The central protocol is

```text
AU ** credits
  -- open, outer -> inner -->
exists x. alpha x ** closing x
  -- abort with alpha x, inner -> outer --> AU
  -- commit with beta x y, inner -> outer --> phi x y
```

`x` is observed when the accessor opens, not necessarily when the operation
is called. After abort, another thread can change the abstract state before
the next attempt. `beta` must express the actual abstract operation; `phi`
is the client's continuation after that operation. Abort is a logical
restoration of resources, not rollback of arbitrary physical effects.
Commit consumes the closing capability; it is not duplicated to keep an
abort branch for later.

The `forall*` over `option b` encodes an **additive** choice over that one
capability. It must not be replaced with separating conjunction of two
continuations: both alternatives may capture the same exclusive ownership.
In contrast, `forall+` in the queue's storage proof owns a separating
collection of distinct physical next fields.

`Update.wand` hides owned resources plus pure existence of suitable ghost
code. Pure code availability does not make captured resources persistent.
Likewise, an AU's reusable step witness does not duplicate its hidden state.
`Triple.from_invariant` captures a client invariant and `extra`; it lends
`alpha x` to the implementation and keeps `residual x` for the callback.
On commit, the callback must rebuild the whole client invariant and produce
`phi`, not just update some detached ghost variable.

### Relationship to Iris, TaDA, and HoCAP

These are design correspondences, **not mechanized embeddings or
equivalence theorems between logics**.

| Existing notion | Correspondence here | Important difference or gap |
| --- | --- | --- |
| Iris mask-changing fancy update | `Update.fupd`, derived from a resource-capturing ghost `wand` | Masks track open invariants with opposite polarity; this is not Iris's primitive modality or its entire rule set. |
| Iris atomic accessor (`atomic_acc`) | `Atomic.accessor`, exposing alpha with an additive abort/commit choice | Credits and Pulse locality are explicit; the API uses two ordinary witness types rather than Iris's telescope notation. |
| Iris atomic update (`atomic_update`) | `Atomic.atomic_update`, with abort restoring the hidden retry state | The existential state/step construction supplies introduction and reusable opening, not a proof of equivalence to Iris's greatest-fixed-point definition. |
| TaDA abstract atomicity | An implementation can take many steps while exposing one abstract alpha-to-beta transition to clients | No TaDA region/guard calculus, abstract-atomic triple syntax, or translation of its proof rules is implemented. |
| HoCAP-style client ghost code and resource protocols | `Triple.from_invariant` takes a client `finish` callback; payload predicates and the helping descriptor carry client-chosen resources | This is a particular invariant-backed constructor, not the full HoCAP logic or a general higher-order concurrent protocol framework. |
| Authoritative ghost state with persistent observations | Queue history authority, monotone snapshots, and agreeing model halves | Uses Pulse's existing ghost-reference APIs; there is no new generic Iris camera/resource-algebra layer. |

TaDA combines abstraction over *when* an operation takes effect with
abstraction over *which* data it owns. The examples exercise both: FIFO state
changes at a successful link/head CAS, while payload resources cross the
queue boundary at that same logical point. The FIFO abstract specification
is stronger than memory safety or a count invariant.

The HoCAP connection concerns allowing clients to refine resource protocols
by supplying ghost code at synchronization points. That callback need not
run on the calling thread: the `Helping` descriptor arranges for a winning
worker to construct and commit it. The queue's tail helping is a different,
weaker phenomenon: it repairs representation after enqueue has committed.
Neither mechanism automatically establishes liveness.

Primary references:

* Iris's maintained
  [`iris.bi.lib.atomic`](https://plv.mpi-sws.org/coqdoc/iris/iris.bi.lib.atomic.html)
  definitions of atomic accessors and updates, and the
  [Iris project](https://iris-project.org/).
* Pedro da Rocha Pinto, Thomas Dinsdale-Young, and Philippa Gardner,
  [*TaDA: A Logic for Time and Data Abstraction*](https://www.doc.ic.ac.uk/~pg/publications/daRochaPinto2014TaDA.html),
  ECOOP 2014, DOI `10.1007/978-3-662-44202-9_9`.
* Kasper Svendsen, Lars Birkedal, and Matthew Parkinson,
  [*Modular Reasoning about Separation of Concurrent Data Structures*](https://cs.au.dk/~birke/papers/hocap-conf.pdf),
  ESOP 2013, DOI `10.1007/978-3-642-37036-6_11`, introducing HoCAP.
  The paper builds on Jacobs and Piessens's client ghost-code approach;
  the callback idea is not unique to HoCAP.

## Mask and resource discipline

Masks name **currently open invariants**: their polarity is opposite to Iris's
available-invariant masks, and they are not Pulse's `opens` footprint.
Opening adds a name; closing removes it. Reopening an already-open name is
rejected. Closing need not be LIFO, but `Masks.run` requires a balanced mask
before control returns to ordinary Pulse code. Composition permits at most
one observable action.

Every attempt supplies fresh later credits. Abort restores the atomic update,
**not** the spent credits. An ordinary invariant needs one credit per opening.
The counter buys credits separately for its load and CAS attempts.

An arbitrary atomic update is not automatically sendable: its hidden state
may contain thread-local ownership. The helping example uses the existing
`SendableTrade` combinator to transfer a capability capturing sendable resources
and construct the update on the winning helper.

## Examples and validation

The relocated [examples directory](../../../share/pulse/examples/logical_atomicity)
contains the following modules (all prefixed `Pulse.Lib.LogicalAtomicity.Example`):

* `Counter`: load/CAS-loop modular UInt32 fetch-and-add; failed attempts abort,
  successful CAS commits. A client proves the old value is zero and advances
  its ghost state to one.
* `Read`: a read-only linearization point and a client proving the value is 37
  without changing the abstract state.
* `Masks`: open `i`, open `j`, close `i`, close `j`, using explicit combinators.
* `Helping`: two workers compete for a descriptor. Only the winner executes
  the operation; the caller receives its result and exclusive payload
  ownership, joins the helpers, and frees the descriptor.
* `Rejections`: double opening, escaping an open mask, two observable steps,
  missing credits, double commit, abort after commit, and automatic transfer
  of an arbitrary atomic update.
* `MSQueue.*`: an intrusive Michael--Scott MPMC FIFO queue, with ownership
  transfer, CAS retries, tail helping, and sequential and concurrent clients.

### Michael--Scott queue

The queue uses an immutable arena of cells and UInt32 node IDs, because Pulse's
existing atomic primitives are UInt32-based. Each cell has an immutable payload
value and an atomic next field. ID `0xffffffff` is null; node zero is the initial
dummy. Enqueue consumes a **one-use node ticket**, backed by exclusive ownership
of that node's next field, and the payload resource `P value`. Nodes are neither
reclaimed nor reused. Thus this example has a finite lifetime allocation budget,
not an unbounded allocator or a recycling bounded queue.

The public logical-atomic specifications are sequence-based:

* Enqueue changes `xs` to `xs ++ [value]` and transfers `P value` into the queue.
* Successful dequeue changes `value :: xs` to `xs` and returns `P value`.
* Empty dequeue proves that the abstract sequence was empty.

`MSQueue.Model` proves the append-only history and FIFO sequence lemmas.
`Storage` manages physical links and exclusive tickets. `State` connects head,
tail, retained links, payload ownership, and a client model half-reference.
Monotonic ghost snapshots justify using stale observations without ABA or
prophecies. `Enqueue` commits at the successful link CAS; `Dequeue` commits at
the successful head CAS or a null-next read. Tail CAS operations help structural
progress but do not change the abstract sequence or commit another operation's
client continuation. Dequeue reads head, next, then tail; the snapshot proof
justifies this ordering and avoids a second head-validation load.

`MSQueue.Actions` combines an open client update with one atomic implementation
step and delays its closing action until the implementation invariant is
restored. The client's open mask must exclude the queue invariant. Failed CAS
attempts restore the update and any untransferred ownership; each attempt buys
fresh credits for both invariants.

Start with `MSQueue.Clients.fst`: `fifo_ownership` proves exact FIFO results,
recovers two exclusive boxed payloads, and frees them; `delayed_tail` exposes the
scheduling point after linking; `stale_tail_retry` exercises a stale link CAS.
`MSQueue.Rejections` checks that an enqueue ticket cannot be reused and that a
transferred payload cannot be read before ownership is returned.
`MSQueue.Concurrent.fst` constructs updates from a shared client invariant and
verifies a two-producer/two-consumer task-pool client. Each worker constructs its
own update from sendable resources; no arbitrary-update sendability is assumed.
The concurrent client establishes safe sharing and uses the FIFO operation
contracts, but does not additionally prove a closed-world permutation theorem
for its two returned values or final emptiness; the executable test checks
those results. Similarly, `delayed_tail` and `stale_tail_retry` prove their
final empty models, but the diagnostic booleans are checked at runtime rather
than refined to `true` in their F* postconditions. These are explicit client
specification gaps, not gaps in the sequence-based operation contracts.

Suggested queue reading order: `Model` -> `Storage` -> `State` -> `Actions` ->
`Enqueue`/`Dequeue` -> `Clients`/`Concurrent`. `Atomics.fsti` states the primitive
assumptions already supplied by Pulse; its two verified implementations and
the handwritten `MSQueue_atomics.ml` explain the model/runtime boundary.
`Rejections` records expected failures for resource misuse.

### Build, editor support, and runtime checks

From the F* repository root:

```sh
make -j$(nproc) 3
make -C pulse/share/pulse/examples/logical_atomicity -j$(nproc)
```

The first command verifies and installs the foundational libraries and model;
the examples are now checked by the second command and by the parent
`pulse/share/pulse/examples` target, not by the library build. Use `verify`
instead of the default `all` target for proof-only checking, or `runtime-test`
to request the executable regression target (which depends on the proofs).
Generated artifacts stay in `pulse/build/logical_atomicity`.

The local `Pulse.fst.config.json` selects the installed stage-3 compiler and
source/core include paths for editing this directory. The Makefile uses core
includes for verification only: extraction must use the installed/native
realizations rather than accidentally selecting core semantic implementations.
Neither the editor configuration nor the Makefile enables admits.

The default target extracts and runs OCaml regression tests, including failed CAS, wraparound,
read-only behavior, and 32 two-helper runs. Queue regressions cover FIFO payload
recovery, stale and deliberately failed CAS attempts, delayed tail helping,
a producer paused after linking while another producer helps, 64
two-producer/two-consumer runs, and 16 native four-producer/four-consumer batches
of 64 distinct payloads each. The repeated verified clients reuse one task pool:
the existing `Task.teardown_pool` establishes logical completion but does not
yet stop its worker threads. The native stress-test workers are explicitly
joined.

The handwritten OCaml harness is not itself verified and must respect erased
preconditions such as one-use node tickets and disjoint producer IDs. Its
sorted-result comparisons check loss/duplication for executed schedules,
not every concurrent FIFO history or all possible schedules. The F* operation
proofs, not the stress tests, establish the sequence transition contracts.

The runtime reuses the native lock, fork, and sleep realizations from the
existing task-pool tests. Queue reads and CAS use the explicit
`MSQueue.Atomics-ocaml.fst` realization in `MSQueue_atomics.ml`, not the ordinary
read/write CAS lowering. This test realization serializes individual atomic
operations with a mutex and can inject permitted spurious CAS failures. It
tests concurrent safety, not lock-free execution. Both F* atomic wrapper
implementations are verified against the existing primitive API; as with other
Pulse primitives, the handwritten target realization is a runtime trust
boundary. No pointer-atomic axiom or checker extension is added.

## Limitations and remaining design work

* **Safety, not progress.** Proofs establish partial correctness, not fairness,
  termination, starvation-freedom, or lock-freedom. A divergent operation's
  postcondition applies if it returns; spurious CAS failure need not cease.
* **Explicit composition.** There is no checker notation, automatic AU
  opening, inferred linearization point, or general atomic-triple proof mode.
  The abstraction remains a library of explicit, verified combinators.
* **Footprints.** Current executable examples use `run_closed`, exposing
  `all_inames`; they cannot be called inside an already-open lexical invariant.
  Selective client footprints can be derived through the mask-parametric
  `run` API, but corresponding convenient operation wrappers are not supplied.
* **Modal rules.** Only the update rules exported by `Update.fsti` are
  available. A complete Iris-style derived-rule collection (mask weakening,
  richer framing/quantifier rules, later interaction, and generalized triple
  elimination) is not provided or claimed automatically.
* **Client construction.** `Triple.from_invariant` handles one invariant,
  one credit per opening, and an empty-footprint ghost continuation. More
  general multi-invariant clients can use the lower-level primitives, but
  there is no packaged general constructor for them here.
* **Thread transfer.** AU state is not automatically sendable. The descriptor
  example transfers a `SendableTrade` recipe; queue workers construct AUs
  locally from shared handles. General helping must justify captured-resource
  transfer rather than assume it.
* **Queue lifetime.** The immutable list arena has finite one-use IDs.
  Draining returns payloads but not node tickets. No destructor, reclamation,
  reuse/ABA treatment, or constant-time arena lookup is proved.
* **Future-dependent linearization.** There are no prophecy variables or
  retrospective-commit rules. The intended Herlihy--Wing queue FIFO proof
  remains deferred rather than being approximated by a weaker bag contract.
* **Runtime trust.** Existing primitive/extraction contracts and handwritten
  target realizations remain boundaries of the executable story. The queue
  OCaml backend is mutex-based; weak-memory atomics and native lock-freedom
  are outside this validation.
