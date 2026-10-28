# Logical atomicity

This is a library-only prototype: no Pulse syntax, elaboration, or checker
changes. The semantic model and all combinators are verified; there are no new
axioms or admitted proofs.

Foundations live in this directory. The separate
[examples guide](../../../share/pulse/examples/logical_atomicity/README.md)
provides a simple-to-complex reading order, worked examples, implementation
details, and executable validation instructions. Each source file documents
its proof role, definitions, and limitations.

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
In contrast, `forall+` owns a separating collection of resources, one for
each quantified element.

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
| HoCAP-style client ghost code and resource protocols | `Triple.from_invariant` takes a client `finish` callback and captures client-owned resources | This is a particular invariant-backed constructor, not the full HoCAP logic or a general higher-order concurrent protocol framework. |

TaDA combines abstraction over *when* an operation takes effect with
abstraction over *which* data it owns. Here, an AU lets the implementation
expose one abstract transition while interacting with client-owned resources.
The alpha/beta contract must describe the intended operation, not merely
memory safety.

The HoCAP connection concerns allowing clients to refine resource protocols
by supplying ghost code at synchronization points. The `finish` callback
captures resources and must reestablish the client invariant. Executing it
on another thread requires a separate justification for transferring those
resources; the AU interface does not supply generic sendability or liveness.

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

An arbitrary atomic update is not automatically sendable: its hidden state
may contain thread-local ownership. Transferring an operation requires a
protocol that justifies moving its captured resources, or construction of
the update at the destination from already-sendable ownership.

## Building and examples

From the F* repository root, verify and install the foundational libraries
and model:

```sh
make -j$(nproc) 3
```

Examples are separate from the library build. See the
[examples README](../../../share/pulse/examples/logical_atomicity/README.md)
for the reading order, queue design and proof structure, example-specific
limitations, editor setup, and proof/extraction/runtime commands.

## Limitations and remaining design work

* **Safety, not progress.** Proofs establish partial correctness, not fairness,
  termination, starvation-freedom, or lock-freedom. A divergent operation's
  postcondition applies if it returns; spurious CAS failure need not cease.
* **Explicit composition.** There is no checker notation, automatic AU
  opening, inferred linearization point, or general atomic-triple proof mode.
  The abstraction remains a library of explicit, verified combinators.
* **Footprints.** `run_closed` exposes `all_inames` and cannot be called inside
  an already-open lexical invariant. Selective client footprints can be
  derived through the mask-parametric `run` API, but corresponding convenient
  operation wrappers are not supplied.
* **Modal rules.** Only the update rules exported by `Update.fsti` are
  available. A complete Iris-style derived-rule collection (mask weakening,
  richer framing/quantifier rules, later interaction, and generalized triple
  elimination) is not provided or claimed automatically.
* **Client construction.** `Triple.from_invariant` handles one invariant,
  one credit per opening, and an empty-footprint ghost continuation. More
  general multi-invariant clients can use the lower-level primitives, but
  there is no packaged general constructor for them here.
* **Thread transfer.** AU state is not automatically sendable. General helping
  must justify captured-resource transfer rather than assume it.
* **Future-dependent linearization.** There are no prophecy variables or
  retrospective-commit rules; clients requiring future-dependent reasoning
  need additional support.
* **Runtime trust.** Existing primitive/extraction contracts and handwritten
  target realizations remain boundaries of the executable story. The
  examples guide documents the concrete backends and their limitations.
