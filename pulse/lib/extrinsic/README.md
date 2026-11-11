# Extrinsic separation logic over PulseCore

This directory develops a small, deeply embedded HeapLang, an independent
operational semantics over PulseCore heaps, and a separation logic proved
sound for arbitrary concurrent schedules.

**Program proofs use the source-logic interface in
[HeapLang.Proof.fsti](Pulse.Extrinsic.HeapLang.Proof.fsti).
Adequacy is a theorem of that interface, proved once for all programs in
[HeapLang.Adequacy](Pulse.Extrinsic.HeapLang.Adequacy.fsti).**

The client examples finish with Hoare triples. They do not mention logical
memories, physical heaps, source transitions, execution traces, native actions,
or per-program budget/adequacy arguments. The semantic implementation of the
logic is responsible for those concerns.

The interface supports typed postconditions, structural rules, composition
through every HeapLang evaluation context, fork, addition, equality,
conditionals, load, store, mask-aware atomic triples, and composable ghost mask
updates. Invariant examples include both nested opening and an invariant whose
body is another invariant handle. Physical allocation, CAS, and loops still
need client-facing primitive rules.

Core logic lives directly in this directory. The [examples](examples) directory
contains source-program proofs, example-specific assertion definitions,
negative interface tests, and explicitly separate operational regressions.

## Reading guide

Read the numbered sections in order for a foundations-to-programs tour.
Each section identifies files and declarations to visit, explains the proof
obligation discharged there, and connects it to the next layer. Where a
module has both `.fsti` and `.fst`, read the contract before its implementation.
Module names below omit the `Pulse.Extrinsic` prefix unless stated otherwise.

| Stop | What to establish before moving on |
| --- | --- |
| [1. PulseCore foundations](#1-pulsecore-foundations) | Which assertions, heaps, levels, and invariant operations are reused? |
| [2. Independent operational model](#2-the-independent-operational-model) | What can a source program do, without reference to the logic? |
| [3. Guarded fixed points](#3-guarded-fixed-points) | How can recursive WPs be defined as existing PulseCore assertions? |
| [4. Resource WP](#4-the-resource-wp) | What does ownership of a WP promise about every next source step? |
| [5. Composition](#5-composition-and-generic-rules) | Why can triples be composed without re-proving reductions? |
| [6. Native bridges](#6-native-heap-and-action-bridges) | How do native heap operations and mask actions meet source semantics? |
| [7. Atomic source logic](#7-atomic-source-logic-and-invariants) | How do mask updates and atomic proofs support invariant opening and closing? |
| [8. Typed interface](#8-the-typed-source-logic-interface) | Which rules can a program proof use without semantic arguments? |
| [9. Uniform adequacy](#9-adequacy-once-for-the-logic) | Why does any such proof imply safety under arbitrary schedules? |
| [10. Source proofs](#10-source-level-proof-walkthroughs) | How do the rules prove sequential and invariant-sharing programs? |

The conceptual dependency structure is:

```text
PulseCore assertions -> Guarded -----------+
                                          |
Language + HeapLang + heap relations ----> WP ----> generic Adequacy
                                          |
                         context/bind and structural rules
                                          |
PulseCore heap/mask actions -> bridges -> Updates -> AtomicLogic
                                          |
                                   HeapLang.Proof
                                     /         \
                     HeapLang.Adequacy           source Hoare proofs
```

This is a reading order, not a literal build graph. Adequacy and client
proofs are separate consumers of the logic: **a client proof does not depend
on the adequacy module**. The build obtains the actual module dependencies
from F*.

For a client-only reading, jump to [stop 8](#8-the-typed-source-logic-interface)
and then [stop 10](#10-source-level-proof-walkthroughs). The complete tour is
for understanding or extending the implementation as well.

Reference sections follow the tour:
[module map](#11-module-map-and-abstraction-boundaries),
[remaining work](#12-remaining-work), and [building](#13-building).

## 1. PulseCore foundations

**Read:** [PulseCore.Heap.fsti](../core/PulseCore.Heap.fsti),
[PulseCore.IndirectionTheorySep.fsti](../core/PulseCore.IndirectionTheorySep.fsti),
[PulseCore.IndirectionTheoryActions.fsti](../core/PulseCore.IndirectionTheoryActions.fsti),
and [PulseCore.Masks.fsti](../core/PulseCore.Masks.fsti).
These are existing foundations outside this directory, not a second model
introduced for HeapLang.

### 1.1 Physical heaps and logical memories

Start with `PulseCore.Heap.heap`, `pts_to`, `select`, and `interp`. A physical
heap contains cells governed by PCMs. HeapLang will choose one particular PCM
for integer cells; it does not replace the underlying heap model.

Then distinguish that heap from `IndirectionTheorySep.mem` and `full_mem`.
Logical memories also carry the bookkeeping used for guarded reasoning and
invariants. The generic WP takes a projection from full logical memories to
source states. The concrete projection for HeapLang is supplied at
[stop 6](#6-native-heap-and-action-bridges).

Keep the following notation in view throughout the tour:

| Notation | Meaning |
| --- | --- |
| `S` | `PulseCore.IndirectionTheorySep`. |
| `S.slprop` | The existing resource-assertion type. |
| `P ** Q` | Separating conjunction, written `S.star P Q` in many proofs. |
| `P \|-- Q` | Entailment, written `S.implies P Q`. |
| `S.interp P m` | Assertion `P` holds in logical memory `m`. |
| `physical m` | The source state represented by a full logical memory. |
| `inv i P` | A duplicable handle for an invariant, not ownership of its body. |
| `E` | A mask naming currently **open** invariants. |

### 1.2 Assertions, heredity, and affinity

Read `emp`, `pure`, `star`, the separating existential, `implies`, `later`,
and `age_hereditary`. The resource assertions already have the hereditary
and affine properties needed here. Heredity permits aging; affinity permits
discarding resources. Neither permits duplicating exclusive cell ownership.

For the representation behind these contracts, follow `hereditary`,
`mem_pred_affine`, `slprop_ok'`, and `mk_slprop` in
[IndirectionTheorySep.fst](../core/PulseCore.IndirectionTheorySep.fst).
`slprop_ok'` conjoins the two closure properties; `mk_slprop` packages a
predicate satisfying them. The underlying memory representation and levels
come from [KnotInstantiation](../core/PulseCore.KnotInstantiation.fsti).
These internals matter when constructing WP, not when proving client triples.

There are two distinct quantities in the accounting:

```text
level m
budget m = level m - credits m - 1
```

Strictly smaller **levels** justify recursive logical reasoning. A lower
bound on the remaining **budget** lets adequacy cover a given number of
physical source steps. These are not source-language variables or counters
that client programs must maintain.

### 1.3 Invariants and masks

Read `inv`, `somewhere`, and `mem_invariant` in `IndirectionTheorySep`, then
`new_invariant` in `IndirectionTheoryActions`. Finally read `action`,
`gaction`, `open_invariant`, and `close_invariant` in `Masks`.

The ambient assertion `mem_invariant E m` accounts for the closed invariant
resources while excluding the names in `E`. Thus `E = empty` means **all
invariants are closed**, not that no invariant exists.

Opening adds a name to the mask and exposes `somewhere (later P)`; closing
requires that exposed body and removes the name. The later and locality
conditions are part of the existing core contract. The extrinsic development
must preserve them, not replace opening by an entailment `inv i P |-- P`.

At this point the reusable foundations are in place. What remains to define
is a source language and a logic connecting these assertions to its steps.

## 2. The independent operational model

**Read in order:** [Language](Pulse.Extrinsic.Language.fst),
[HeapLang](Pulse.Extrinsic.HeapLang.fst),
[HeapLang.Memory](Pulse.Extrinsic.HeapLang.Memory.fst), and
[HeapLang.Semantics](Pulse.Extrinsic.HeapLang.Semantics.fst).

### 2.1 The generic language and scheduler

In `Language`, follow `language`, `reducible`, `not_stuck`, `config`,
`pool_step`, `execution`, `safe`, and `main_returns`.

The `language` record contains expressions, values, states, value recognition,
and a primitive step relation. A step produces a residual expression, a new
state, and a list of spawned expressions. Its only value-related obligation
is `values_stuck`: a value does not reduce.

`pool_step.Schedule` selects any thread and appends its children to the
remaining pool. Terminated threads remain in place, so thread zero stays the
main thread. `execution l n c c'` witnesses `n` actual pool steps.
`safe` says that each thread is a value or can step in the current shared
state; `main_returns` observes thread zero only.

No ownership, WP, or invariant assertion appears in these definitions.
In particular, the scheduler is not restricted to schedules chosen by proofs.

### 2.2 Deep syntax and substitution

In `HeapLang`, follow `ty`, `value`, `var`, `expr`, `rename`, `subst`,
`substitute`, and `to_val`, then the typed `context` datatype and `fill`.
Evaluation contexts are source syntax, so client composition rules can
mention them without importing the operational semantics.

`HeapLang.expr g t` is syntax indexed by a typing context `g` and result type
`t`. The types are unit, booleans, mathematical integers, and references to
integer cells. Variables are typed de Bruijn indices. A `Let` body is another
syntax tree, not an F* continuation. `rename`, `subst`, and `substitute`
implement capture-avoiding substitution.

The constructors are:

```text
Val, Var, Let, If, Seq, Add, Eq,
Alloc, Load, Store, Cas, Fork, While
```

The language is first-order: there are no function values, higher-order store,
general recursive functions, deallocation, or join handles. `While` can
diverge. `Fork` starts a unit-returning child and returns unit without joining.

Intrinsic typing rules out ill-typed syntax, but does not prove memory safety:
a reference value need not designate an allocated cell. The logic supplies
the ownership and invariant conditions needed for safe execution.

### 2.3 Physical state and primitive heap relations

In `HeapLang.Memory`, follow `cell_value`, `cell_pcm`, `contents`,
`unchanged_except`, `allocation`, `store`, and `cas`. Then read
`contents_unique`, `store_unique`, `points_to`, `allocate`, and `write`.

The source heap is `PulseCore.Heap.heap u#3`, not a separate finite-map model.
`HeapLang.Memory` instantiates an exclusive integer-cell PCM with elements
`Empty` and `Full n`. Two `Full` elements cannot compose.

`contents h r v` observes a cell in that heap. `allocation`, `store`, and `cas`
are relations on physical heaps. A store preserves the heap extent and every
other address. A successful CAS does likewise; a failed CAS leaves the whole
heap unchanged. `store_unique` establishes uniqueness of a store's target
heap.

Allocation is relational. A native allocator constructs one valid witness,
but the source reduction relation is not defined by running that allocator.
Any logical allocation rule will have to account for every allowed source
allocation, not just the chosen witness.

### 2.4 Reductions, contexts, and the generic-language instance

In `HeapLang.Semantics`, read `head_step` and `step`. Continue with
`invert_head`, `invert_let`, `invert_seq`, and the general `invert_fill`.
`compose` and `fill_compose` describe composition of source contexts.
Finally read `packed_expr`, `packed_value`, `packed_step`, and `language`.

`HeapLang.Semantics.head_step` defines primitive reductions.
`ContextStep` places one in a deep evaluation context. The contexts specify
evaluation order; `While` unfolds to an `If` and a sequence.

`Pack` and `PackValue` hide the result-type index when instantiating the generic
`Language.language`. These packages are internal to the semantic proof layer;
the client interface exposes postconditions over `value t`.

The inversion lemmas are important later: they characterize **all** steps
of a compound expression, rather than merely constructing one permitted
step. `transition`, `read_transition`, `beta_transition`, and `store_atomic`
package such facts for logical-rule implementations.

The optional [Examples](examples/Pulse.Extrinsic.Examples.fst) module exercises this
model directly. [Safety](Pulse.Extrinsic.Safety.fst) gives a separate bounded
operational safety formulation. Neither is the source-program proof interface
or a prerequisite for understanding the resource WP.

The output of this stop is an independent notion of execution against which
soundness can be stated. Native-action pre/postconditions have not defined
what it means for a source program to run.

## 3. Guarded fixed points

**Read:** [Guarded.fsti](Pulse.Extrinsic.Guarded.fsti), then
[Guarded.fst](Pulse.Extrinsic.Guarded.fst).

### 3.1 The missing ingredient is a fixed point, not a new assertion model

The WP of a non-value must refer to the WPs of its residual expression and
spawned children. This recursion is not structural recursion on source
syntax: loops can unfold to larger syntax and threads can spawn.

`family a` is simply `a -> S.slprop`. `agrees_below n p q` says that two
families agree on every memory of level less than `n`. Read `contractive`:
an operator turns agreement below `n` into agreement below `n + 1`.
The refined type `operator` requires this property.

Existing heredity and affinity do not, on their own, define the recursive
family or prove its equation. This module constructs that family **within**
the existing assertion model.

### 3.2 Follow the construction

Read these implementation declarations in order:

1. `iterate` starts from the constant `emp` family and applies the operator
   finitely many times.
2. `successive` and `stable_from` prove that sufficiently deep approximants
   agree at any fixed lower level.
3. `fix_pred` selects approximant `level + 1` at the memory being examined.
4. `fix` proves this predicate hereditary and affine using PulseCore's
   existing properties, then packages it with `S.mk_slprop`.
5. `fix_approximant` connects the resulting family to the finite
   approximants; `unfold_fix` proves the public equation:

```text
fix f x == f (fix f) x
```

`later_contractive` gives a simple example of contractiveness. The WP will
prove its own operator contractive by placing recursive obligations at
strictly smaller levels. No new fixed-point axiom is assumed.

## 4. The resource WP

**Read:** [WP.fsti](Pulse.Extrinsic.WP.fsti), then
[WP.fst](Pulse.Extrinsic.WP.fst), initially through `wp_lift`.

### 4.1 Identify the parameters and recursive occurrences

Start with `projection`, `post`, `query`, `invariant`, and `children`.
The construction is generic in a `Language.language` and a projection from
full logical memories to that language's states. A recursive query consists
of an expression and its postcondition.

`children` separates the WPs of all spawned threads, each with postcondition
`emp`. It does not discard the obligation to prove those threads safe.
`invariant m` abbreviates `S.mem_invariant empty m`: all invariants must be
closed at ordinary source-step boundaries.

### 4.2 Read the non-value clause inside out

In the implementation, follow `completion`, `continuation`, `obligation`,
and `body_pred`.

The WP is an assertion about an owned resource fragment, not just a
predicate of a complete physical heap. A `completion` ages that fragment
to a positive level and combines it with an arbitrary frame and the closed
invariant resources to obtain a full logical memory.

For a non-value, `body_pred` quantifies over every such completion at every
positive level no greater than the owned fragment's level. In each completion
it demands:

1. **Progress:** the source expression has a reduction in `physical m`.
2. **All-step preservation:** for every permitted reduction, there is a
   logical successor whose projection equals that reduction's target state.
3. **Resource preservation:** that successor owns the residual WP, all child
   WPs, the original frame, and the closed invariant resources.
4. **Accounting:** its level is strictly smaller, and its budget decreases
   by at most one.

The continuation assertion is:

```text
wp residual Q ** children spawned ** frame ** invariant next
```

The order of quantifiers matters. A rule implementation cannot prove safety
by exhibiting one favorable source execution; it must account for **every**
source successor. Quantifying over arbitrary completions and frames is also
what makes this a separation-logic assertion.

At values, the equation is much simpler:

```text
wp (Val v) Q == Q v
```

There is no update modality around this postcondition. This will constrain
ghost allocation at [stop 8](#8-the-typed-source-logic-interface).

### 4.3 Turn the clause into an assertion and a fixed point

Follow `body_hereditary`, `body_affine`, and `body`. Heredity follows from the
quantification over lower levels; affinity uses `completion_weaken` to absorb
additional resources into the completion.

Next read `children_below`, `continuation_below`, `obligation_below`, and
`body_contractive`. The strict level decrease ensures that recursive WP
occurrences only inspect levels at which the candidate families already
agree. `body_operator` packages this proof, and `wp_family` applies
`Guarded.fix`.

Finally, `unfold_wp` gives the recursive equation. This is the concrete use
of the unfolding law established at the previous stop.

### 4.4 The introduction and elimination boundary

Return to the public contracts of `wp_value`, `wp_step`, and `wp_lift`.

| Lemma | How a logic implementer uses it |
| --- | --- |
| `wp_value` | Replace a value's WP by its postcondition. |
| `wp_step` | Extract progress and all-successor obligations from a WP in a full memory. |
| `wp_lift` | Prove a triple by establishing those obligations for every frame and enabled memory. |

`wp_lift` is intentionally semantic: its premise mentions memories and
reductions. It is an implementation tool for deriving rules, **not** the
interface that client program proofs should repeatedly use.

## 5. Composition and generic rules

**Read:** the rest of [WP.fsti](Pulse.Extrinsic.WP.fsti) and
[WP.fst](Pulse.Extrinsic.WP.fst),
[Rules.fsti](Pulse.Extrinsic.Rules.fsti) and
[Rules.fst](Pulse.Extrinsic.Rules.fst), and
[HeapLang.Contexts](Pulse.Extrinsic.HeapLang.Contexts.fst).
For the pure primitive adapters, continue to
[HeapLang.Rules](Pulse.Extrinsic.HeapLang.Rules.fst).

### 5.1 Frame and consequence

In `WP.fst`, follow `frame_at` to `wp_frame`, then `mono_at` to `wp_mono`.
Both proofs recurse on logical memory level. They rearrange the residual
resources while preserving the original source-step obligations and spawned
thread WPs.

`Rules.hoare` defines a generic triple as entailment into WP. Its
`hoare_frame` and `hoare_consequence` package the structural results.
`entails_star`, `entails_pure`, `entails_emp`, and `hoare_pure` are reusable
assertion-level helpers. These helpers do not execute source programs.

### 5.2 The context contract and bind theorem

Read the `WP.context` record before the proof of `wp_bind`. Its fields
require:

| Field | Obligation |
| --- | --- |
| `plug` | Embed a source expression in the context. |
| `resume` and `values` | Identify the plugged expression when the hole contains a value. |
| `nonvalues` | A non-value in the hole gives a non-value overall. |
| `steps` | Lift a hole step, with the same state change and spawned children. |
| `inversion` | Every step of a plugged non-value comes from a hole step. |

The theorem is:

```text
wp e (fun v -> wp (resume K v) Q) |-- wp (plug K e) Q
```

Follow `context_progress`, `bind_at`, and `wp_bind` in that order. At a value,
the context's value law identifies the required continuation. Otherwise the
proof inverts an arbitrary context step, uses the hole's WP to obtain a
successor, and splits off the residual WP. It recurses on that resource at
a strictly smaller level, then reassembles it with the unchanged child WPs,
frame, and invariant resources.

Thus bind is proved once for any context satisfying the record. It is not a
trace induction repeated for each compound program.

### 5.3 Specialize contexts and discharge value reductions

In `HeapLang.Contexts`, follow `plug`, `resume`, `steps`, `inversion`, and
`make_context`. This constructs a generic WP context from **any** typed
HeapLang evaluation context, including nested combinations.

`steps` uses `Semantics.compose` and `fill_compose` to lift a hole step.
`inversion` uses `Semantics.invert_fill`, which recurses through the requested
context and rules out competing evaluation positions. For example, an
`AddRight` context fixes the left operand to a value, so a source reduction
cannot instead occur there.

This covers `LetCtx`, `IfCtx`, `SeqCtx`, both addition and equality positions,
allocation and load operands, both store positions, and all three CAS
positions. The `let_context` and `seq_context` functions are now small
specializations of `make_context`, not separate context proofs.

There is still a source reduction after the hole becomes a value:
`Let (Val v) body` takes a beta step, and `Seq (Val ()) rest` takes a
sequence step. `HeapLang.Rules.wp_beta` and `wp_sequence_value` handle those
reductions. They are not themselves the general bind rules.

Also read `Rules.wp_readonly`, `HeapLang.Rules.wp_transition`, and
`wp_fork`. These lower-level helpers derive rules for physically unchanged
steps, including pure computation and spawning. The name `wp_readonly`
classifies a step's physical-heap effect; it does **not** introduce a
special class of read-only invariants.

At [stop 8](#8-the-typed-source-logic-interface), the typed `let_rule` and
`sequence` combine these value reductions with `wp_bind`. Clients will only
supply the two component triples. `context_rule` exposes the general version.
Having an evaluation-context rule for `Alloc` or `Cas` does not yet provide
the missing primitive rule once all that operation's arguments are values.

## 6. Native heap and action bridges

**Read:** [Atomic.fsti](Pulse.Extrinsic.Atomic.fsti) and
[Atomic.fst](Pulse.Extrinsic.Atomic.fst), then
[HeapLang.Logic.fsti](Pulse.Extrinsic.HeapLang.Logic.fsti) and
[HeapLang.Logic.fst](Pulse.Extrinsic.HeapLang.Logic.fst).

### 6.1 Expose core actions without replacing source semantics

Start with `Atomic.enabled`, `run`, `native`, and `run_native`.
They expose the semantics of existing PulseCore actions in full logical
memories, including their frame, mask, and budget contracts.

Read `realizes` next. Matching native pre/postconditions are not sufficient
to justify a source rule. This extra condition requires progress and says
that **every** source reduction has the native action's returned value and
physical target, with no spawned children.

`with_invariant`, `realizes_with_invariant`, and `wp_atomic` give a
lower-level route from such an action and its correspondence proof to WP.
This bridge remains useful for implementations, but source clients do not
construct these witnesses. The next stop gives a judgment directly about
source expressions instead.

### 6.2 Relate physical ownership to logical ownership

In `HeapLang.Logic`, read `physical`, `ghost_physical`, `points_to`,
`points_to_contents`, and `points_to_intro`.

`physical` projects the concrete heap from a full logical memory.
`points_to` lifts native cell ownership into `S.slprop`. The two ownership
lemmas connect it with physical observations and physical ownership.
`ghost_physical` proves that a core ghost action preserves the projection.

There are deliberately two assertions called `points_to` at different
layers: `HeapLang.Memory.points_to` is physical heap ownership, whereas
`HeapLang.Logic.points_to` is the assertion used in source triples.
Only the latter belongs in ordinary client proofs.

### 6.3 Follow a native write to its source relation

In `HeapLang.Logic.fst`, follow `write_core`, `write_correspondence`, and
`write_memory`. The update uses native `MemoryAlt.upd_gen`, preserves the
arbitrary frame and the mask's invariant resources, and establishes the
independently defined `HeapLang.Memory.store` relation.

`Memory.store_unique` and `Semantics.store_atomic` then identify all allowed
source store results with that physical target. This is the key additional
work beyond reusing a native store's Hoare specification.

The small additions in [PulseCore.Heap.fsti](../core/PulseCore.Heap.fsti)
expose heap extent, extensional equality, and observations of native
allocation/update. They support this correspondence, not new invariant
semantics.

### 6.4 Invariant and initialization support

In `Atomic`, read `open_invariant`, `close_invariant`, `open_unchanged`,
`close_unchanged`, and `allocate_invariant`. Opening and closing are the
actual `PulseCore.Masks` operations, with proofs that their resulting full
memories are unchanged. Ghost allocation can change the logical world but
preserves level and budget; its physical heap is unchanged as well.

In `HeapLang.Logic`, `world` equips a physical heap with a chosen logical
budget and initially empty invariant resources. This is initialization
machinery for generic adequacy, not a task for each program proof.

`points_to_exposed` and `exposed_lift` are general assertion lemmas in this
module. The example predicate `bit_cell` and its entailments instead live in
[ExamplePredicates](examples/Pulse.Extrinsic.ExamplePredicates.fsti). No
bit-specific predicate or witness-extraction helper is part of the core heap
bridge.

## 7. Atomic source logic and invariants

**Read:** [AtomicLogic.fsti](Pulse.Extrinsic.AtomicLogic.fsti), then
[AtomicLogic.fst](Pulse.Extrinsic.AtomicLogic.fst).

### 7.1 A judgment about source steps

Follow `result`, `step_post`, and `hoare`. Suppressing the generic language
and projection parameters, write the judgment schematically as:

```text
atomic E P e Q
```

This is a judgment about the **source expression** `e`, not a native
computation type. It specifies a non-value expression whose every source
reduction returns a value, spawns no children, and restores the indicated mask
and resources.

For every frame and enabled full memory, it requires progress and covers
every source successor. `result` records the returned value, physical
correspondence, restored resources and mask, and level/budget bounds.
Unlike ordinary WP, the successor level may be unchanged; in that case the
budget must not decrease.

There need not be one chosen executable native action witnessing the whole
judgment. This lets `consequence`, `frame`, and `exists_pre` operate on source
proofs, including proofs that depend on logical existential witnesses.

`E` names currently open invariants. `to_wp` embeds an empty-mask atomic
proof into ordinary WP, aging once if the atomic successor has not already
decreased the level. It requires the physical projection to be stable under
aging. Its typed wrapper will be `HeapLang.Proof.atomic_to_hoare`.

An ordinary Hoare triple cannot be used in place of an atomic one. In
particular, knowing that a multi-step program restores a resource at the end
does not justify exposing an invariant across its intermediate steps.

### 7.2 The general invariant rule

Define:

```text
exposed P = somewhere (later P)
```

`AtomicLogic.invariant`, later exposed as
`HeapLang.Proof.atomic_invariant`, has this shape:

```text
i is not in E
atomic (E + i) (exposed P ** R) e
  (fun v -> exposed P ** Q v)
-------------------------------------------------
atomic E (inv i P ** R) e
  (fun v -> inv i P ** Q v)
```

**Its premise is another source-logic proof.** A client neither constructs a
native action nor proves a source/native simulation to invoke this rule.
It is general in the invariant predicate `P`, the frame-like resources `R`,
the postcondition `Q`, and the surrounding mask.

The invariant predicate remains the same across opening and closing; the
resources or existential witness establishing it can change. There is no
separate notion of a "mutable invariant."

The rule preserves PulseCore's actual later and locality obligations. It does
not assert `inv i P |-- P` or identify `somewhere (later P)` with `P` for
arbitrary predicates. A concrete client must discharge those obligations
using valid assertion-level properties.

### 7.3 Follow the soundness argument for opening and closing

Read the implementation of `AtomicLogic.invariant` in this order:

1. Run the core opening action with the ordinary precondition and outside
   frame framed off. `open_unchanged` preserves the full memory, so the
   source state at which the inner proof applies is unchanged.
2. Apply the premise under `E + i`, with the invariant handle itself framed.
   The premise supplies progress and a suitable result for each source step.
3. For each such result, run the core closing action with the client's
   postcondition and outside frame framed off.
4. Use `close_unchanged` to preserve the physical target and accounting, and
   re-establish the outer mask and protected postcondition.

Opening and closing do not introduce scheduler steps. They surround one
value-producing source reduction inside its logical proof; closed invariant
resources are restored before the ordinary WP boundary is exposed.

`AtomicLogic.lift` is the backend entry point for deriving new atomic
primitive rules. Its semantic callback belongs in the rule implementation,
not in the invariant-using client.

### 7.4 Compose explicit ghost mask updates

**Read:** [Updates.fsti](Pulse.Extrinsic.Updates.fsti) and
[Updates.fst](Pulse.Extrinsic.Updates.fst), then `AtomicLogic.updates`.
The typed interface exposes the judgment as:

```text
update E1 E2 P Q
```

An update transforms logical resources and the open mask without taking a
source step. Its interpretation quantifies over arbitrary frames and enabled
full memories, supplying a successor with the same physical heap and budget,
a non-increasing level, and the postcondition under the new mask.

The update judgment is available even at budget zero. That matters when a
source step consumes the final unit of budget and an invariant must still be
closed afterward. The atomic source step itself still requires positive
budget.

Read `entails`, `trans`, `frame`, and `exists_pre` for the structural
calculus. Then read `open_invariant`, `close_invariant`, `allocate`, and
`later_elim` for the core-backed updates. Allocation returns the assertion
`allocated P = exists* i. inv i P`. Later elimination has the explicit cost:

```text
update E E (later P ** later_credit 1) P
```

It uses the actual core later-elimination action. Spending that credit and
decreasing the level preserves the budget; it is not an axiom that later
can be erased.

`AtomicLogic.updates`, exposed as `P.atomic_updates`, composes updates around
an atomic source proof:

```text
update E1 E2 P P'
atomic E2 P' e Q'
forall v. update E2 E1 (Q' v) (Q v)
-----------------------------------
atomic E1 P e Q
```

The first update preserves the source state in which the primitive step is
proved; the second preserves that step's target. Their masks must match and
the outer mask must be restored. `Updates.bind_wp`, exposed as
`P.update_hoare`, also permits a closed-to-closed update before an arbitrary
**non-value** source program.

These are composable update **judgments**, not an assertion-valued fancy-update
modality. Ordinary WP remains closed-mask and still has the unmodified value
equation. In particular, `update_hoare` cannot justify ghost allocation at a
value; that larger change to WP remains separate work.

## 8. The typed source-logic interface

**Read:** [HeapLang.Proof.fsti](Pulse.Extrinsic.HeapLang.Proof.fsti), then
[HeapLang.Proof.fst](Pulse.Extrinsic.HeapLang.Proof.fst).
This is the boundary between the semantic implementation and program proofs.

### 8.1 Typed triples and postconditions

Use the following aliases when reading the examples:

```fstar
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module R = Pulse.Extrinsic.Rules
module S = PulseCore.IndirectionTheorySep
```

The interface has the following shape:

```text
post t = value t -> slprop
wp e Q : slprop
hoare P e Q = P |-- wp e Q
```

`wp` is abstract in the interface. A client cannot unfold its interpretation
without deliberately crossing the abstraction boundary. The Hoare triple is
an entailment, not a datatype of derivations and not the assertion that some
unrelated `stt` computation has a matching pre/postcondition.

In the implementation, `packed_post` adapts a typed postcondition to generic
packed values. A value with the wrong type tag receives postcondition
`pure False`. `wp` specializes the generic WP to the packed source expression
and `C.physical`; `atomic` similarly specializes `AtomicLogic.hoare`.
Clients need neither packing nor projection arguments.

The named postcondition combinators are:

| Combinator | Assertion at returned value `v` |
| --- | --- |
| `constant_post P` | `P` |
| `returns_value expected` | `pure (v == expected)` |
| `framed_post Q F` | `Q v ** F` |
| `prepend_post P Q` | `P ** Q v` |
| `read_post r old` | `points_to r old ** pure (v == old)` |

Naming these functions also avoids unnecessary function-equality obligations
when composing F* proofs.

### 8.2 Structural and composition rules

| Rule | Logical use |
| --- | --- |
| `value_rule` | Prove `{P} Val v {Q}` from `P \|-- Q v`. |
| `consequence` | Strengthen the precondition and weaken the postcondition. |
| `frame` | Preserve an additional separating resource. |
| `pure_pre` | Use a pure fact in the precondition while proving the remaining triple. |
| `let_rule` | Compose a bound expression with its substituted continuation, for every returned value. |
| `sequence` | Compose an arbitrary unit-returning first program with the rest. |
| `context_rule` | Compose through any typed source evaluation context, including nested contexts. |
| `fork` | Split resources between the parent and a child proved with postcondition `emp`. |

The composition rules are genuinely general:

```text
{P} e {M}
forall v. {M v} substitute v body {Q}
-----------------------------------
{P} Let e body {Q}

{P} first {fun _ -> M}       {M} rest {Q}
---------------------------------------
{P} Seq first rest {Q}
```

The first expression need not already be a value, need not preserve the
physical heap, and may spawn children. In `Proof.fst`, follow `let_rule`
and `sequence`: they combine packed postcondition reasoning, `WP.wp_mono`,
the context's `WP.wp_bind`, and the corresponding value reduction.
`fork` adapts the already-derived packed fork rule.

For arbitrary `k : context a b`, the general rule is:

```text
{P} e {M}
forall v. {M v} fill k (Val v) {Q}
--------------------------------
{P} fill k e {Q}
```

Only source syntax and component triples occur in this interface. The
continuation premise includes any remaining primitive reduction, such as an
addition, store, or branch selection. Clients do not supply step-lifting or
inversion certificates.

### 8.3 Primitive rules and their implementations

The ordinary load and store specifications are:

```text
{ r |-> old } Load r
{ v. r |-> old ** pure (v == old) }

{ r |-> old } Store r desired
{ _. r |-> desired }
```

`add` and `eq` prove the exact arithmetic or boolean result on value operands.
`if_value` derives a conditional triple from the selected branch's triple.
Combining it with `context_rule (IfCtx Hole yes no)` handles an arbitrary
condition computation. Frame and consequence adapt these specifications to
a larger program.

To connect these convenient contracts to the earlier layers, read
`primitive_result`, `atomic_load`, and `atomic_store` in `Proof.fst`.
The load implementation uses ownership to establish physical contents and
then characterizes every source read. The store implementation calls
`C.write_memory` and `Semantics.store_atomic` to connect the native update
to every source store result.

Both atomic rules work under an arbitrary open mask. The ordinary `load`
and `store` rules instantiate them at the **empty** mask and then use
`atomic_to_hoare`; they do not silently close an arbitrary caller's mask.

No client has to supply `contents`, `store`, `packed_step`, a native action,
or a correspondence certificate to use these primitives.

### 8.4 Ghost invariant allocation

`P.allocate_invariant` is also a source-logic rule:

```text
e is not a value
forall i. {inv i P ** R} e {Q}
--------------------------------
{P ** R} e {Q}
```

It lets the proof allocate an invariant from owned resources, rather than
requiring the client to construct a logical world with an invariant already
installed. The invariant name is a proof-level name, not a source-language
value or instruction.

The non-value condition is significant. The rule absorbs the ghost update at
the next source step. The current WP value equation has no general update
modality around the postcondition, so this is not an unrestricted update rule
at values.

In `Proof.fst`, follow `allocate_invariant`. It uses `WP.wp_lift`, runs the
native invariant allocator, proves the physical state unchanged, invokes
the supplied logical continuation for the fresh name, and applies
`WP.wp_step` in the updated world. Level and budget preservation make this
a valid obligation for the original world.

This is allocation of a **logical invariant**, not the source-language
`Alloc` instruction. A client-facing rule for physical cell allocation is
still missing.

### 8.5 Check the boundary with negative examples

[ProofRejections](examples/Pulse.Extrinsic.ProofRejections.fst) checks that the public
source interface rejects:

- Reopening a name already in the open mask.
- Turning an open-mask atomic proof into an ordinary triple.
- Closing without restoring the exposed invariant body.
- Opening around an ordinary Hoare proof instead of an atomic source proof.
- Eliminating later without providing a later credit.
- Treating an opening update as a closed-to-closed update.
- Applying `update_hoare` at a value.

The positive invariant examples use the neighboring legal rules. The
rejections check the source interface, not just the types of native actions.

## 9. Adequacy once for the logic

**Read:** [Adequacy.fst](Pulse.Extrinsic.Adequacy.fst), then
[HeapLang.Adequacy.fsti](Pulse.Extrinsic.HeapLang.Adequacy.fsti) and
[HeapLang.Adequacy.fst](Pulse.Extrinsic.HeapLang.Adequacy.fst).

Before using the interface to prove examples, close the soundness argument.
This layer relates *any* triple to the independent executions from stop 2.
It does not inspect the syntax or proof of a particular example.

### 9.1 Give each thread its resources

In generic `Adequacy`, follow `children`, `pool`, `selected_post`, `others`,
`pool_decompose`, and `pool_reassemble`.

`pool` assigns the main thread its specified postcondition and every other
thread postcondition `emp`. When the scheduler selects a thread,
`pool_decompose` isolates that thread's WP and frames all other thread
assertions. `pool_reassemble` restores the pool after the step, including
newly spawned threads.

This is why the fork rule needed a child WP rather than just permission
to discard the child's resources.

### 9.2 Preserve the pool for any schedule

Continue with `represents`, `represents_framed`, `preserve_step_framed`,
and `preserve_execution_framed`.

The representation connects the physical configuration to a full logical
memory holding the pool assertion and closed invariants. A preservation step:

1. Decomposes the pool around whichever thread `Schedule` selected.
2. Uses `WP.wp_step`, framing all other threads and the external frame.
3. Obtains a logical successor matching that actual source step.
4. Reassembles the residual and child WPs, losing at most one unit of budget.

`preserve_execution_framed` iterates this argument over an arbitrary
execution. An initial budget of at least `n + 1` leaves a positive budget
after `n` steps.

Finally read `pool_safe`, `pool_result`, `adequate`, and
`adequate_realizable`. Positive budget permits extracting progress for any
non-value thread; the value equation extracts the main thread's postcondition
if it has returned. This is the one generic induction on execution traces.
Program proofs will not repeat it.

### 9.3 Relate the typed interface to generic adequacy

The public typed theorem has this schematic form:

```text
realizable h P
hoare P e Q
forall v. Q v |-- pure (phi v)
execution n ([e], h) last
----------------------------------------------------------
safe last
and, if main returns, its value has e's type and satisfies phi
```

The expression, assertion, postcondition, observation, execution length, and
schedule are all parameters.

Read `realizable` in `HeapLang.Adequacy.fst`: for every requested budget,
there must be a full logical memory with the **same physical heap** `h`,
enough budget, and ownership of `P ** closed invariants`. This is a
satisfiability condition on the precondition, not an assumption that the
program is already safe.

Now follow `adequate`:

1. Use consequence to reduce the arbitrary postcondition `Q` to the desired
   pure observation `phi`.
2. Choose a realization with budget at least `n + 1`.
3. Turn the initial precondition into the typed WP, keeping closed invariant
   resources framed.
4. Use the private packing adapter to apply generic `Adequacy.adequate`.
5. Unpack a returned value. A wrong type tag has postcondition `pure False`;
   a matching tag yields the desired typed value and `phi`.

Only the implementation uses `friend` access to the typed WP representation.
The adequacy statement is about the public logical judgment.

### 9.4 Initialize once, instantiate for any program

Read `points_to_realizable` and `adequate_points_to`.
`points_to_realizable` uses `HeapLang.Logic.world` and `points_to_intro` to
establish realizability from physical ownership. `adequate_points_to`
packages that initialization with the uniform theorem.

The final example at stop 10 supplies a triple for `concurrent_readback`
starting from ordinary points-to ownership and returning a bit. To obtain
an operational corollary, instantiate `adequate_points_to` with that program,
its proved triple, and `phi v = (v == 0 \/ v == 1)`. There is no need to add a
`concurrent_adequate` proof, recreate worlds or budgets in the example, or
analyze its schedules.

The result is partial correctness and safety under arbitrary scheduling.
Because the execution length and execution are arbitrary, every finite
reachable prefix is covered. This does not assert termination, fairness,
liveness, joining, or general linearizability. Main returning does not imply
that every child has finished.

## 10. Source-level proof walkthroughs

**Read in order:** [LogicExamples](examples/Pulse.Extrinsic.LogicExamples.fst),
[InvariantExamples](examples/Pulse.Extrinsic.InvariantExamples.fst),
[MaskExamples](examples/Pulse.Extrinsic.MaskExamples.fst), and
[NestedExamples](examples/Pulse.Extrinsic.NestedExamples.fst).

None of these program-proof modules imports the operational semantics, WP
implementation, or adequacy module. The only reasoning beyond calls to
`HeapLang.Proof` is ordinary separation entailment, pure reasoning, and
source-level substitution.

### 10.1 Load, compute, and retain ownership

`LogicExamples.sequential r` is:

```fstar
Let (Load (Val r)) (Add (Var Here) (Val 1))
```

`sequential_correct` proves:

```text
{ r |-> old }
  sequential r
{ result. pure (result == old + 1) ** r |-> old }
```

Follow `increment_result`, `sequential`, and `sequential_correct`:

1. Name `p = points_to r old` and the desired framed result postcondition.
   `S.sep_laws` supplies the ordinary separation equalities.
2. `P.load r old` establishes the bound expression's triple with postcondition
   `read_post r old`.
3. Introduce an arbitrary returned integer `v`. The continuation precondition
   is now `p ** pure (v == old)`.
4. `assert_norm` calculates substitution in the deep syntax, yielding
   `Add (Val v) (Val 1)`. It is not a transition proof.
5. `P.pure_pre` makes `v == old` available while checking the continuation.
   Inside it, `P.add v 1` establishes the exact sum, and `P.frame` preserves
   `p`. The equality identifies the desired result with `old + 1`.
6. `P.let_rule` combines the load triple and the universally quantified
   continuation triple.

There is no callback proving a load or `Let` transition.

### 10.2 Store followed by load

`LogicExamples.round_trip r desired` is:

```fstar
Seq (Store (Val r) (Val desired)) (Load (Val r))
```

Its entire proof is:

```fstar
P.store r old desired;
P.load r desired;
P.sequence (C.points_to r old) (C.points_to r desired)
  (Store (Val r) (Val desired)) (Load (Val r)) (P.read_post r desired)
```

The postcondition retains ownership and identifies the returned integer.
This tests composition across a genuine heap-changing operation, rather than
only across pure reductions.

Read the three calls as an ownership flow:

```text
points_to r old
  -- store --> points_to r desired
  -- load  --> points_to r desired ** pure (result == desired)
```

The middle assertion is exactly what `P.sequence` connects. No physical
successor heap appears in this proof.

### 10.3 Compute inside arithmetic, store, and conditional contexts

Continue in `LogicExamples`:

| Program | Triple established | Contexts exercised |
| --- | --- | --- |
| `load_plus r = Add (Load r) 1` | Returns `old + 1` and retains `r |-> old`. | `AddLeft` |
| `increment r = Store r (load_plus r)` | Changes `r |-> old` to `r |-> old + 1`. | `StoreRight`, composed with the preceding proof |
| `zero_test r = Eq 0 (Load r)` | Returns exactly whether `old` is zero, retaining ownership. | `EqRight` |
| `set_if_zero r` | Sets a zero cell to one; otherwise preserves its old value. | `IfCtx`, composed with `zero_test_correct` |

Read `load_plus_correct` first. It uses `load`, introduces the returned value,
uses `pure_pre` to expose its equality with `old`, proves the framed addition,
and applies `context_rule`. Unlike the earlier `Let` example, the load is
directly inside the arithmetic expression.

`increment_correct` then uses that entire triple as the premise for a
`StoreRight` context. For each computed integer, `pure_pre` makes its value
known, and `store` proves the continuation. This is a genuine heap-changing
read/compute/write program, not a pure-context demonstration.

Finally follow `zero_test_correct` and `set_if_zero_correct`. The former uses
`eq` under a frame. The latter uses the boolean equality in the intermediate
postcondition to select either the store triple or the value triple;
`if_value` proves the branch step and `context_rule` composes the condition.
No operational lemma is invoked by any of these proofs.

### 10.4 Prepare an invariant with a changing witness

Return briefly to `bit`, `bit_point`, `bit_cell_unfold`, `bit_cell_intro`,
and `bit_cell_exposed` in
[ExamplePredicates.fsti](examples/Pulse.Extrinsic.ExamplePredicates.fsti).

The assertion library defines `bit_cell r`, with a proved unfolding equation:

```text
bit_cell r == exists* (n : int{n == 0 \/ n == 1}). points_to r n
```

`bit_cell_intro` packages an owned bit-valued cell into that existential.
`bit_cell_exposed` supplies entailments in both directions between this
particular predicate and its exposed form.

The latter is an assertion-level lemma justified by native timelessness and
locality properties of lifted heap predicates. It is not a generic way to
discard `later` or `somewhere`, and the general invariant rule is not limited
to this predicate.

### 10.5 Prove an invariant-protected write

In `InvariantExamples`, `write_inv` derives:

```text
{ inv i (bit_cell r) }
  Store r desired
{ _. inv i (bit_cell r) }

where desired is either 0 or 1
```

The reusable proof is now `write_atomic_inv`, parameterized by any outer mask
not already containing the invariant name. `write_inv` specializes it to the
empty mask and calls `atomic_to_hoare`. Follow the helper from top to bottom:

1. Set `body = bit_cell r`, `handle = inv i body`, and
   `mask = outer + i`. The inner postcondition is `exposed body ** emp`;
   the writer has no additional result resource to return.
2. Use `bit_cell_unfold`, `bit_cell_intro r desired`, and
   `bit_cell_exposed` to prepare the entailment from ownership of the desired
   value to the restored exposed body.
3. For each old witness `old : bit`, invoke `P.atomic_store` under the open
   mask. `P.atomic_consequence` changes its points-to postcondition into the
   required restored-body postcondition.
4. `P.atomic_exists` discharges the existential precondition. This is logical
   existential elimination, not extraction of a value from a semantic memory.
5. Another atomic consequence adapts `exposed body ** emp` to that
   existential precondition, using the assertion lemmas from step 2.
6. `P.atomic_invariant` wraps the inner source proof with the invariant rule,
   returning to the outer mask and preserving the handle.
7. Simplify the postcondition by atomic consequence. Only the closed-mask
   `write_inv` wrapper then applies `P.atomic_to_hoare`.

The old witness and desired witness may differ. The invariant predicate
does not change; the resource establishing it does.

### 10.6 Prove an invariant-protected read with a useful result

Next read `bit_result` and `read_inv`. The postcondition is:

```text
inv i (bit_cell r) ** pure (result == 0 \/ result == 1)
```

The proof follows the write's structure, with an additional result argument:

1. For each witness `old : bit`, `P.atomic_load` gives ownership of the cell
   and `pure (v == old)`.
2. `bit_cell_intro` and `bit_cell_exposed` restore the exposed body from the
   unchanged ownership.
3. `R.entails_pure` derives `v == 0 \/ v == 1` from `v == old` and the
   refinement on `old`. `R.entails_star` combines this fact with the restored
   body, producing `exposed body ** bit_result v`.
4. Use atomic consequence, existential elimination, and the general invariant
   rule as before; then embed the closed-mask proof into ordinary Hoare logic.

This proves a property of the returned value, rather than merely that the
read is well typed. The ownership is returned to the invariant, not retained
by the reader alongside the handle.

### 10.7 Share the invariant between competing writers

`InvariantExamples.concurrent r` is:

```fstar
Seq (Fork (Store (Val r) (Val 0))) (Store (Val r) (Val 1))
```

Follow `concurrent_correct`:

1. Let `p = inv i (bit_cell r)`. `S.dup_inv_equiv` supplies `p == p ** p`.
2. `write_inv r 0 i` proves the child store preserves `p`.
3. `R.entails_emp` and `P.consequence` weaken the child's postcondition to
   `emp`, as required by the fork rule.
4. `P.fork p p child` gives one handle to the child proof and retains the
   other in the parent. Duplication of the handle makes `p` sufficient for
   the fork's `p ** p` precondition.
5. `write_inv r 1 i` proves the parent store, and `P.sequence` composes it
   after the fork.

The exclusive points-to assertion is never duplicated. Only the invariant
handle is shared. There is no schedule enumeration or fork-transition proof
in this argument.

### 10.8 Compose a readback without assuming a join

`concurrent_readback r` adds a final load:

```fstar
Seq (concurrent r) (Load (Val r))
```

`concurrent_readback_correct` calls `concurrent_correct`, calls `read_inv`,
and connects their common invariant-handle assertion with `P.sequence`.
The child is not joined, so the main thread's write does not determine the
readback value. The specification correctly permits either bit, without
requiring the proof to know when the child writes.

### 10.9 Allocate the invariant from ordinary ownership

Finally, `concurrent_from_owned` starts with **ordinary cell ownership**:

```text
{ points_to r initial }
  concurrent_readback r
{ result. pure (result == 0 \/ result == 1) }

where initial is either 0 or 1
```

Follow the final proof:

1. Apply `P.allocate_invariant` with body `bit_cell r`, additional resource
   `emp`, and the whole non-value source program.
2. For the fresh name supplied to its logical premise, use
   `concurrent_readback_correct`.
3. Use affinity and `P.consequence` to drop the returned invariant handle,
   retaining only `bit_result`. This does not duplicate or expose its cell.
4. `bit_cell_intro r initial` strengthens the allocated-body precondition
   from `bit_cell r` to the initial points-to assertion.
5. Finish with `P.consequence`.

The completed theorem is a Hoare triple. It does not initialize a semantic
memory, choose a budget, or prove adequacy for this program. Its operational
meaning comes from the already-proved theorem at
[stop 9](#9-adequacy-once-for-the-logic).

### 10.10 Use mask updates directly

In [MaskExamples](examples/Pulse.Extrinsic.MaskExamples.fst),
`allocate_two` composes two ghost allocations. It frames the untouched
resource around each allocation and connects the intermediate assertions
with `update_trans`:

```text
update empty empty (P ** Q) (allocated P ** allocated Q)
```

This is a ghost-resource proof, not a source instruction or a claim that the
existential names are distinct.

`read_with_updates` proves an exact-value read from an invariant protecting
`points_to r old`, using separate opening and closing rules:

1. `open_invariant` changes the empty mask to `{i}`.
2. `points_to_exposed`, `update_entails`, and `update_trans` turn the exposed
   body into cell ownership, retaining the handle.
3. `atomic_load` and `atomic_frame` prove the read under `{i}`.
4. For each returned value, frame its equality fact around `close_invariant`.
   Entailment and transitivity adapt the read's resources to that closing
   update.
5. `atomic_updates` combines opening, the source read, and closing;
   `atomic_to_hoare` exports the ordinary triple.

`allocate_and_read` starts with ordinary points-to ownership and ends with
`pure (result == old)`. It first uses `update_allocate`. For every name in the
resulting existential, `read_with_updates` supplies the source triple.
`update_exists` and `update_trans` connect these proofs, and `update_hoare`
absorbs the closed update before the load. Its intermediate assertion uses
the abstract `P.wp`; the proof never unfolds it or constructs a logical
memory.

### 10.11 Open nested invariants without erasing later

In [NestedExamples](examples/Pulse.Extrinsic.NestedExamples.fst), read
`nested_open`, `nested_handle_write`, and `nested_concurrent`.

`nested_open` opens two distinct invariants around the same source store.
It calls `write_atomic_inv` while the first name is already in the mask,
frames the first exposed body around that proof, and then closes the outer
invariant with `atomic_invariant`. Both handles are preserved; the inner
bit-cell witness may change.

`nested_handle_write` exercises a stronger form of nesting: the outer
invariant's **body is the inner invariant handle**. Its specification is:

```text
{ inv i (inv j (bit_cell r)) ** later_credit 1 }
  Store r desired
{ _. inv i (inv j (bit_cell r)) }

i and j are distinct; desired is a bit
```

Opening the outer invariant exposes `somewhere (later (inv j ...))`, not a
plain inner handle. The proof proceeds as follows:

1. `Rules.exposed_inv` removes only the location wrapper, using the core
   locality property of invariant handles. The **later remains**.
2. `update_later_elim` consumes the supplied credit to obtain the inner
   handle under the outer open mask.
3. `write_atomic_inv` opens and closes the inner invariant for the store.
4. `entails_later` restores the guarded inner handle. `atomic_updates`
   composes the credit-consuming update, source proof, and restoring update.
5. `atomic_invariant` closes the outer invariant; consequence adapts the
   postcondition, and `atomic_to_hoare` yields the displayed triple.

The proof does not assume invariant handles are timeless. Nor does it
manufacture a credit: the specification explicitly requires one.

`nested_concurrent` uses this triple for the two competing writers. It starts
with the outer handle and two separately owned credits, duplicates only the
handle, gives one credit to each thread, and applies `fork` and `sequence`.
The postcondition retains the outer handle. The credits are consumed by the
respective nested openings, including under arbitrary interference.

These are source-level proofs. The generic adequacy theorem is unchanged;
operational corollaries still require a realization of their stated
preconditions, including the credits where present.

### 10.12 Keep operational regressions separate

[Examples](examples/Pulse.Extrinsic.Examples.fst) contains independent regression
examples for the source semantics: allocation/store/load, a main result with
a looping child, and a CAS interleaving.

Those are tests of the language model, not the method used to verify client
programs. In particular, the CAS traces are not a client-facing separation
logic verification of CAS; that primitive's logical rule remains to be added.

## 11. Module map and abstraction boundaries

All names in the table have prefix `Pulse.Extrinsic`.

| Module | Responsibility |
| --- | --- |
| [Language](Pulse.Extrinsic.Language.fst) | Generic reductions, thread pools, executions, and observations. |
| [HeapLang](Pulse.Extrinsic.HeapLang.fst) | Typed deep syntax and substitution. |
| [HeapLang.Memory](Pulse.Extrinsic.HeapLang.Memory.fst) | Physical cell PCM and heap-operation relations. |
| [HeapLang.Semantics](Pulse.Extrinsic.HeapLang.Semantics.fst) | Independent reductions and their structural properties. |
| [Guarded](Pulse.Extrinsic.Guarded.fsti) | Contractive assertion families and fixed points. |
| [WP](Pulse.Extrinsic.WP.fsti) | Generic operational WP, lifting, framing, monotonicity, and bind. |
| [Rules](Pulse.Extrinsic.Rules.fsti) | Generic entailments and Hoare rules; also backend lifting helpers. |
| [HeapLang.Contexts](Pulse.Extrinsic.HeapLang.Contexts.fst) | Generic WP-context instance for every typed HeapLang evaluation context. |
| [HeapLang.Rules](Pulse.Extrinsic.HeapLang.Rules.fst) | Lower-level packed-value rules and semantic lifting helpers. |
| [Atomic](Pulse.Extrinsic.Atomic.fsti) | Lower-level native action and invariant adapters. |
| [HeapLang.Logic](Pulse.Extrinsic.HeapLang.Logic.fsti) | General heap/assertion bridges and exposure lemmas. |
| [Updates](Pulse.Extrinsic.Updates.fsti) | Frame-preserving ghost mask updates, composition, allocation, and later elimination. |
| [AtomicLogic](Pulse.Extrinsic.AtomicLogic.fsti) | Generic masked atomic source judgments and their rules. |
| [HeapLang.Proof](Pulse.Extrinsic.HeapLang.Proof.fsti) | Typed client-facing Hoare and atomic source rules. |
| [ProofRejections](examples/Pulse.Extrinsic.ProofRejections.fst) | Negative checks at the source-logic interface. |
| [Adequacy](Pulse.Extrinsic.Adequacy.fst) | Generic thread-pool preservation and soundness. |
| [HeapLang.Adequacy](Pulse.Extrinsic.HeapLang.Adequacy.fsti) | Once-for-all adequacy for that interface and reusable initialization. |
| [ExamplePredicates](examples/Pulse.Extrinsic.ExamplePredicates.fsti) | Example-specific bit-cell assertions and entailments, outside the core logic. |
| [LogicExamples](examples/Pulse.Extrinsic.LogicExamples.fst) | Sequential source proofs, including arithmetic, store, equality, and conditional contexts. |
| [InvariantExamples](examples/Pulse.Extrinsic.InvariantExamples.fst) | General invariant-rule clients, concurrent composition, and logical allocation. |
| [MaskExamples](examples/Pulse.Extrinsic.MaskExamples.fst) | Composable ghost allocation and explicit source-level opening/closing updates. |
| [NestedExamples](examples/Pulse.Extrinsic.NestedExamples.fst) | Nested masks and invariant-containing-invariant proofs, including concurrent writers. |
| [Examples](examples/Pulse.Extrinsic.Examples.fst) | Operational regression examples, not client program proofs. |
| [Safety](Pulse.Extrinsic.Safety.fst) | A separate purely operational bounded-safety formulation. |

Do not confuse the three rule-related modules: `Rules` supplies generic
entailments and backend rules; `HeapLang.Rules` is the packed, semantic
adapter layer; `HeapLang.Proof` is the intended source-program rule API.
The client examples use entailments from the first and triples from the
last, not semantic lifting callbacks from the middle.

The semantic implementations use `friend` access where representations are
needed. `ExamplePredicates.fst` also accesses assertion representations to
prove its unfolding and exposure lemmas; it does not prove program traces.
The four program-proof modules use neither `friend` nor semantic lifting
helpers. Core logic modules never import example modules.
`HeapLang.Adequacy` alone connects the abstract typed WP to the generic
operational adequacy theorem.

The development introduces no admitted proof or new axiom; it relies on the
existing F*/PulseCore foundations.

## 12. Remaining work

The current interface is a usable slice, not the final framework.

- Add source-level primitive rules for physical allocation, CAS, and loops.
  Their operand contexts are supported, but a context rule does not supply
  the primitive specification.
- Develop an assertion-valued fancy-update modality and its interaction with
  WP values if needed. The current mask updates are composable judgments;
  ordinary WP remains closed-mask, and its update-introduction rule requires
  a non-value expression.
- Extend the nested examples with additional ghost-state protocols and
  initialization lemmas for their resource preconditions. The current
  invariant-containing-invariant example explicitly uses later credits.
- Derive logical atomicity or atomic-update specifications for multi-step
  implementations. The current `atomic` judgment concerns a single
  value-producing source step; it is not such a specification.

These extensions should preserve the boundary established here: semantic
work belongs in rule implementations and generic soundness, while program
proofs should be compositions of logical rules.

## 13. Building

From the F* repository root, with the local compiler already built:

```sh
make -C pulse -j16 lib-extrinsic
```

The opt-in target is defined in
[pulse/Makefile](../../Makefile) and
[mk/lib-extrinsic.mk](../../mk/lib-extrinsic.mk). It checks all `.fst` and
`.fsti` roots and their core/common dependency closure. The default cache is
`pulse/build/lib.extrinsic.checked`. The target is not added to the default
build, CI, or installation targets.
The root discovery includes `examples/`, and the target adds that directory
to its include path; the core library does not depend on it.

To use an installed compiler:

```sh
make -C pulse -j16 lib-extrinsic \
  FSTAR_EXE=/absolute/path/to/bin/fstar.exe \
  FSTAR_LIB=/absolute/path/to/lib/fstar \
  INCLUDE_PATHS=
```

Set both paths to the same installation. Clearing `INCLUDE_PATHS` avoids
implicitly using this checkout's stage2 checked-library path with an external
compiler.

To check from a fresh cache and refresh Z3 between queries:

```sh
make -C pulse -j16 lib-extrinsic \
  FSTAR_EXE=/absolute/path/to/bin/fstar.exe \
  FSTAR_LIB=/absolute/path/to/lib/fstar \
  INCLUDE_PATHS= \
  CACHE_DIR="$PWD/pulse/build/lib.extrinsic.fresh.checked" \
  OTHERFLAGS="--z3refresh --print_expected_failures"
```

Choose a new cache directory: an existing cache still reuses up-to-date checked
files. `--print_expected_failures` displays the intended diagnostics from
`ProofRejections`; inspect them as well as their annotated error classes.

This is a verification target, not a HeapLang interpreter or extracted
executable. Check the whole target rather than only an example leaf: the
interfaces and their implementations both need verification.
