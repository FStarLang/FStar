# Cached big atomics: failure helping

This example adapts **Cached-WaitFree** from Daniel Anderson, Guy E. Blelloch,
and Siddhartha Jayanti's
[Big Atomics, Algorithm 1](https://arxiv.org/pdf/2501.07503) and the pinned
[Iris mechanization, `CachedWaitFree.v`](https://github.com/cmuparlay/bigatomic-mechanization/blob/251ff8b71e0879f561c729115e972b7a6d3ce0af/theories/CachedWaitFree.v).
It verifies a two-word cached load and **strong value-CAS**, using the existing
LAT library without new axioms, admits, or checker changes. The algorithm and
failure-helping proof structure are credited to those sources; the upstream
Iris development's MIT notice is retained in [LICENSE.Iris](LICENSE.Iris).

The CAS follows the reference's control flow: one cached read, at most two
backup-publication attempts, and **false after both attempts fail**, without
retrying the read. The proof ports the pending-request registry and failure
helping rather than weakening the strong CAS contract. Finite immutable backup
nodes replace allocation and reclamation.

## Why failure helping is necessary

The reference has a ghost registry of pending CAS requests. When a successful
publication first changes their expected value, it commits their failure
continuations. This matters for an A--B--A execution: a stale pointer CAS can
fail even though the value at that failure is again A. Simply committing
`false` at that point would not establish the strong value-CAS postcondition.

The registry owns the actual AU, not just a historical-value certificate.
Its pending, completed, and collected states correspond to the reference's
`cas_inv`; `forall+` owns the separating collection corresponding to
`registry_inv`. `Registry.publish` commits the successful caller, then
`help_all` implements `linearize_cas`: each still-pending caller commits false
against the new value. Completed results survive subsequent publications.
An exclusive receipt token prevents collecting a continuation twice.

Client continuations remain arbitrary. They are stored as `on caller AU`,
which is placeless even when the AU's captured resources are not sendable.
The new verified [`Locality`](../../../../../lib/pulse/logical_atomicity/Pulse.Lib.LogicalAtomicity.Locality.fsti)
rules exchange placeless abstract state with a helper while leaving the
captured state, closing continuation, and result at the caller's locality.
`Masks.localize` derives ghost-only mask-changing impersonation from the
existing semantic locality lemmas; it cannot execute another thread's physical
operations. Saved-proposition references store the higher-order postconditions
without putting large propositions into the first-order request log.

CAS AUs use `outer = {q.name}`: the implementation invariant is already open,
as in the reference's exclusion of the implementation namespace from the AU's
enabled mask. A client-invariant constructor uses
`Triple.from_invariant (Q.mask q) client_name ...`. Each AU restores the common
outer mask before another opens. No pairwise-disjointness assumption about
different clients' masks, sendability assumption on captured state, new axiom,
or prophecy is used.

## Contracts and reading order

All module names below start with `Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree`.

1. **[`Model`](Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Model.fst) and
   [`State`](Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.State.fst).**
   A marked backup always names the current immutable value, even while the
   cache is stale or partly overwritten. An unmarked backup agrees with a
   completed cache at an even version. An append-only history and monotonic
   versions support stale observations; a fractional writer token permits
   only one cache writer. The external `model q v` is half of the abstract
   value's ghost ownership, not ownership of either cache word.

2. **[`Read`](Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Read.fst).**
   `beta q old result` preserves `model q old` and proves `result == old`.
   The operation loads version, first word, second word, and backup. At the
   backup load it commits the AU for that node's immutable value. If the
   backup is unmarked it checks the final version; `Model.cached_read` then
   proves that both separately loaded words match the committed value.
   Otherwise it follows the captured backup. Like the Coq `read'`, this
   fallback does not reload the backup pointer; the C++ standalone load in
   the paper instead performs a fresh protected read on its slow path.
   No prophecy or retrospective commit is used.

3. **[`CAS`](Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.CAS.fst),
   [`Registration`](Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Registration.fst),
   [`Attempt`](Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Attempt.fst), and
   [`Registry`](Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Registry.fst).**
   At commitment, `ok` is exactly `old = expected`; the model becomes
   `desired` on success and stays `old` on failure. At the captured-backup
   load, mismatches and equal-value no-ops commit immediately. A prospective
   change aborts that accessor and registers the AU with its observation and
   reserved opening credits. Successful publication commits both the winner
   and all pending losers within the same single-observable-step action.
   The second pointer CAS tolerates unmarking alone. `two_failures` proves
   that losing both attempts implies a different backup identity, so the
   registry must already contain this caller's failure result.

4. **[`Validate`](Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Validate.fst).**
   Publication has already committed. The writer tries to acquire its
   *original* even version, stores the two cache words separately, releases
   the next even version, and tries to unmark its own backup. A delayed old
   writer cannot overwrite a newer cache, and a failed unmark cannot validate
   a different node. `published`, `held`, and `released` are distinct
   capabilities; the [rejection cases](Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Rejections.fst)
   guard these distinctions and reject duplicating the writer token.

5. **[`Clients`](Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Clients.fst).**
   Owned-state clients prove exact reads, A--B--A changes, a failed comparison,
   and a successful no-op. The latter two retain their unused node tickets.
   Shared clients construct their AUs locally from a separate client
   invariant; both shared handles are proved duplicable and sendable.
   `cas_shared_local` captures a non-sendable `loc caller` assertion and an
   exclusive ghost marker. Its callback checks that it executes at the
   original caller's ghost locality and returns the marked completion there.
   Rejection cases also rule out sending that captured state, duplicating a
   request token, or collecting a result without its token.

[`Storage`](Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Storage.fst)
supplies immutable arena values and one-use publication tickets. Freshness
follows from ghost permission incompatibility, not an assumed no-ABA axiom.
Equal values at different node IDs are allowed. The generic mask-composition
and owned-AU helpers are reused from the queue's `Actions` module.

## Build and executable regressions

From the repository root, with the branch's stage-3 installation available:

```sh
make -C pulse/share/pulse/examples/logical_atomicity/cached_wait_free -j2
```

`verify`, `runtime-test`, and `clean` are also available; the parent
`logical_atomicity` targets recurse into this directory. Artifacts stay in
`pulse/build/logical_atomicity/cached_wait_free`.

The [OCaml harness](runtime_test.ml) runs the verified sequential client,
64 two-writer races, and eight forced schedules: a torn cache copy, delayed
cache installation, replacement of a captured backup, a failed final unmark,
an unmark-only race handled by the second publication attempt, A--B--A before
both attempts, A--B--A between attempts, and one publication helping three
pending callers. The helping cases use `cas_shared_local` and check that no
caller restarts its read. Gates pause domains only between primitives.
The concurrent outcome assertions supplement the verified operation contracts;
the harness and its erased-precondition discipline are not themselves verified.

## Limits and native trust boundary

- Two UInt32 cache words are independently accessed; no wide atomic load/CAS
  is assumed. Versions and encoded node IDs are mathematical naturals, as
  in the Coq model, so counter wraparound is excluded rather than solved.
- Backup nodes form a finite, immutable arena. A successful changing CAS
  consumes one node's ticket; failure or a no-op returns it. There is no
  identity reuse, hazard-pointer implementation, reclamation proof, or
  destructor. List-based arena lookup also precludes the paper's time/space
  bounds.
- CAS has no retry loop. No quantitative wait-free, fairness, or weak-memory
  theorem is asserted. `run_closed` still exposes `all_inames`; client AU
  constructors must respect the implementation-open outer mask.
- [`Atomics`](Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Atomics.fst)
  uses the same existing `as_atomic` model boundary as Pulse's primitives.
  Its strong single-cell exchange returns the actual old value and never
  fails spuriously. The explicitly selected
  [OCaml realization](CachedWF_atomics.ml) serializes individual primitives
  with a mutex, **not whole big-atomic operations**. Those externs are a
  handwritten trust boundary, not a verified native wait-free backend.
