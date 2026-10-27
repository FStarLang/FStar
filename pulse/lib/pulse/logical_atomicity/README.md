# Logical atomicity

This is a library-only prototype: no Pulse syntax, elaboration, or checker
changes. The semantic model and all combinators are verified; there are no new
axioms or admitted proofs.

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

`examples/` contains:

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

From the F* repository root:

```sh
make -j$(nproc) 3
make -C pulse/lib/pulse/logical_atomicity/examples -j$(nproc)
```

The first command verifies the libraries, model, and examples. The second also
extracts and runs OCaml regression tests, including failed CAS, wraparound,
read-only behavior, and 32 two-helper runs. It reuses the native lock, fork,
and sleep realizations from the existing task-pool tests. These are smoke
tests, not a concurrent stress test of the specification-level CAS lowering.

This prototype proves partial correctness, not fairness, termination, or
lock-freedom. Current executable examples use `run_closed` and therefore expose
`all_inames` as their atomic footprint; they cannot be called from an already
open lexical invariant. More selective client footprints and additional
derived Iris-style rules can be built on the mask-parametric `run` interface.
