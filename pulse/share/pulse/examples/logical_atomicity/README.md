# Logical atomicity examples

These examples exercise the verified, library-only logical atomicity API.
Start with the [library README](../../../../lib/pulse/logical_atomicity/README.md)
for the foundational layers, alpha/beta/phi protocol, mask polarity, and
connections to Iris, TaDA, and HoCAP. This guide covers the examples themselves:
what to read, what each proof establishes, and how to run them.

All F* module names below have the prefix
`Pulse.Lib.LogicalAtomicity.Example`. The examples are separate build roots,
not part of the installed library's `fstar.include`. Each source file has
module- and definition-level documentation.

## Reading order: simple to complex

1. **[Read](Pulse.Lib.LogicalAtomicity.Example.Read.fst): one read-only
   linearization point.** Read `alpha`, `beta`, and `read_attempt`, then
   `client`. The load commits an atomic update (AU) without changing the
   abstract state; the client proves its result is exactly 37. This is the
   smallest complete example of opening an AU and returning its continuation.

2. **[Counter](Pulse.Lib.LogicalAtomicity.Example.Counter.fst): retries around
   a successful CAS.** Follow `read_attempt`, `try_attempt`, `fetch_add`, and
   `client_once`. The preliminary load aborts its AU; a successful CAS commits
   a modular UInt32 increment, while failed CAS attempts restore the AU.
   The client proves the old value is zero and advances its ghost state to
   one. Each opening needs fresh credits, including aborted attempts.

3. **[Masks](Pulse.Lib.LogicalAtomicity.Example.Masks.fst): inspect the
   non-lexical mechanism.** `non_lifo` opens `i`, opens `j`, closes `i`, then
   closes `j`; `balanced` returns to ordinary Pulse code. There is no physical
   operation here. The challenge is explicit mask/resource composition:
   invariant lifetimes need not be stack-shaped, but all openings must balance.

4. **[Rejections](Pulse.Lib.LogicalAtomicity.Example.Rejections.fst): learn the
   safety boundaries.** Positive controls accompany expected failures for
   double opening, escaping an open mask, composing two observable steps,
   missing credits, double commit, abort after commit, and automatically
   sending an arbitrary AU. Inspect the resources each illegal use lacks,
   rather than treating an expected error as an admitted proof.

5. **[Helping](Pulse.Lib.LogicalAtomicity.Example.Helping.fst): a different
   thread completes the caller's operation.** Follow the descriptor predicates,
   then `claim`, `complete`, `help`, `await`, and `two_helpers`. Two workers
   compete, but only the winner executes the counter operation and commits
   the caller's continuation. The caller receives its result and exclusive
   payload ownership, joins the helpers, and frees the descriptor.
   `SendableTrade` transfers a recipe built from sendable ownership; the winner
   constructs the AU locally. This is a locked protocol, not a lock-free one.

6. **[Cached big atomics](cached_wait_free/README.md): speculative cache
   reads with a committed result.** Adapted from *Big Atomics* and
   `CachedWaitFree.v`, the load commits at the backup-pointer read, then
   proves that its validated cache or immutable fallback returns that value.
   Strong value-CAS and independently interleaved cache installation are
   verified, including the reference's failure-helping registry. CAS returns
   false after two lost publication attempts without retrying; saved,
   caller-local continuations justify failure even across A--B--A changes.

7. **[Concurrent set](concurrent_set/README.md): lock coupling and strong
   concurrent client guarantees.** Start with its public AU interface and
   sequential client, then the Jacobs--Piessens producer/consumer protocol.
   The second removal of a successfully removed key is proved to fail despite
   interference; the finite task client also proves final emptiness.
   This example uses a finite key universe and reusable, per-node-locked
   linked-list nodes. Its guide explains the difference from the paper.

8. **[Michael--Scott FIFO](msqueue/README.md): exact sequence contracts,
   payload transfer, and structural helping.** Start with the owned-state
   clients, then follow the history and snapshot proof through link/head CAS
   linearization and stale-tail helping. The queue guide includes its own
   reading order, concurrent client guarantees and gaps, and native trust
   boundary. Unlike the set, its arena nodes are one-use, not reusable.

## Build and editor support

From the F* repository root:

```sh
make -j$(nproc) 3
make -C pulse/share/pulse/examples/logical_atomicity -j$(nproc)
```

The first command verifies and installs the foundational libraries and model.
The second verifies the small examples and all three child directories,
extracts their executable clients, and runs all four OCaml harnesses. The parent
`pulse/share/pulse/examples` target also includes this directory; the examples
are not checked by the library build.

For proof-only checking:

```sh
make -C pulse/share/pulse/examples/logical_atomicity -j$(nproc) verify
```

The `runtime-test` target requests the executable regressions and depends on
the proofs. Generated artifacts stay in `pulse/build/logical_atomicity`,
with separate `msqueue/`, `concurrent_set/`, and `cached_wait_free/`
cache/output directories.
Each child supports its own `all`, `verify`, `runtime-test`, and `clean`
targets; the parent recurses into all three.
When changing negative cases, use F*'s `--print_expected_failures` option to
inspect the intended missing resource or mask obligation, not just the error
number.

The local [editor configuration](Pulse.fst.config.json) selects the installed
stage-3 compiler and source/core include paths. The [Makefile](Makefile) uses
core includes for verification only: extraction must select installed/native
realizations rather than core semantic implementations. Neither configuration
enables admits.

## Executable validation and trust boundary

[`runtime_test.ml`](runtime_test.ml) covers counter CAS failure and wraparound,
read-only behavior, and 32 two-helper runs. The larger examples have their own
[queue harness](msqueue/runtime_test.ml) and
[set harness](concurrent_set/runtime_test.ml), plus a
[cached-atomic harness](cached_wait_free/runtime_test.ml) with forced
interleavings; their guides describe the runtime coverage and backend assumptions.

The older harnesses reuse existing native lock, fork, and sleep realizations. The
handwritten harnesses are not verified and must respect erased ownership
preconditions. Their observations supplement the F* contracts, rather than
establishing correctness for all schedules. The queue and cached-atomic
handwritten primitive backends are additional trust boundaries documented
in their guides.

`Task.teardown_pool` currently establishes logical completion but does not
stop its native worker threads. The child harnesses reuse task pools;
process exit bounds the older helper tests' pool lifetimes.

## Scope and limitations

These examples establish partial correctness, not fairness, termination,
starvation-freedom, or lock-freedom. An operation's postcondition applies if
it returns; contention or spurious CAS failures can prevent return.

Executable AU attempts use `run_closed` and expose `all_inames`, so they
cannot be called inside an already-open lexical invariant. Thread transfer
requires sendable captured resources or local AU construction, not a generic
sendability assumption.

Representation, allocation, and reclamation limits are documented separately
in each child guide. Weak-memory atomics and native lock-free backends are
outside this validation. There are no prophecy variables or retrospective-commit
rules; the intended Herlihy--Wing FIFO example remains deferred rather than
weakened to a bag specification.
