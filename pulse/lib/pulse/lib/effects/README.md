# Graded, resource-indexed effects in Pulse

This library has one semantic model: graded computation trees in
`Pulse.Lib.Effects.Core`, with intrinsic support for returning and aborting
operations. `Exception` adds exception layers and handlers. `Rules` derives the
two-exit contracts used by the native exception checker through that same
interpreter. No new logical effect rule is assumed.

Read `Core.fsti`, `Exception.fsti`, and then `Rules.fsti` and its implementation.
The [examples](../../../../share/pulse/examples/effects/README.md) cover ordinary
operations, exceptions, nested framing, grades, native syntax, and rejected uses.
Names below omit the `Pulse.Lib.Effects.` prefix.

## Modules

| Module | Responsibility |
| --- | --- |
| [`Core`](Pulse.Lib.Effects.Core.fsti) ([implementation](Pulse.Lib.Effects.Core.fst)) | Operation protocols, graded trees, composition, framing, consequence, relabeling, and interpretation. |
| [`Exception`](Pulse.Lib.Effects.Exception.fsti) ([implementation](Pulse.Lib.Effects.Exception.fst)) | An abortive exception layer, throwing, forwarding, and handling with ordinary resource-indexed clauses. |
| [`Rules`](Pulse.Lib.Effects.Rules.fsti) ([implementation](Pulse.Lib.Effects.Rules.fst)) | Outcome/tree conversion and derived terminating/divergent two-exit rules; preserves the native result-type convention. |

The earlier policy-based representation has been removed; its development is
available in git history. There is no parallel `Tree` module or compatibility
implementation. Generic programs use `Core.tree ops grade a pre post`;
exception programs use `Exception.prog ops exceptional grade a pre post`.

## Ownership at each node

A tree is a description of code, not an owned live resumption. Constructing or
duplicating it neither executes its actions nor duplicates the ownership needed
to run them. The interpreter requires `pre` and, on normal return of `x`,
establishes `post x`.

Operations are explicitly `Returning input output request reply` or
`Aborting input request`. Their kinds determine which node can invoke them:

| Constructor | Ownership and control |
| --- | --- |
| `Return x` | Entry ownership already satisfies `post x`. |
| `Step action next` | Delay a Pulse action; its result and postcondition establish the next tree's precondition. |
| `Perform op arg next` | Give a returning operation `request arg`, retain a private frame, then resume with `reply arg y ** frame`. |
| `Abort op arg` | Give an aborting operation exactly `request arg`. There is no continuation and no private frame. |

An empty reply type alone does not turn a `Returning` operation into an
`Aborting` one. Exception handlers eliminate actual abortive nodes.

`bind` follows normal leaves and returning continuations; it bypasses its
continuation at an abort. `consequence` uses verified ghost entailments to
change pre/normal postconditions, keeping operation protocols fixed.
`relabel` preserves complete operation descriptors, including kind. It need
not be injective: it establishes protocol compatibility, not nominal identity.

## Framing and exception handling

`Core.frame f` adds `f` to the precondition and normal postcondition and also
transforms the signature:

| Operation kind | Request protocol | Continuation ownership |
| --- | --- | --- |
| Returning | Unchanged | Private frame grows by `f`. |
| Aborting | Strengthened to `request arg ** f` | None; all ownership goes to the abort handler. |

This transforms **every** abortive protocol, including outer exception layers.
It is safe to frame an open throwing computation: its handlers receive the
extra ownership rather than abandoning it in unreachable continuation code.
Resources acquired inside a `Step` are still subject to the same discipline:
return them, transfer them in an exit protocol, or reclaim them before exiting.

`Exception.extend ops exceptional` adds `Throw` with protocol
`Aborting exn exceptional`, and embeds existing operations under `Other`.
`Exception.prog` is just a tree alias. `throw e` requires `exceptional e`.
`handle` takes a normal clause requiring `post x` and an exceptional clause
requiring `exceptional e`; both establish the handler's result postcondition.
No whole-tree frame policy or frame-polymorphic clause is required.

The clauses execute outside the removed layer, so they may re-raise in an
enclosing layer. Other operations are forwarded with their kind and protocols
intact. Tags distinguish layers independently of payload types.

`Exception.frame` exposes the strengthened local and outer contracts.
After removing an inner layer, `framed_layer` presents the already-framed outer
signature as another exception layer. This is a verified protocol-preserving
relabeling, not an ownership proof supplied by the caller.
`Example.Effects.Graded.nested_frame` demonstrates both handlers updating a
cell originally introduced by framing.

## Grades and execution

`Terminating` selects `stt`; `MayDiverge` selects `stt_div`. A grade is a
conservative bound, not a scan of a runtime tree:

| Construction | Grade obligation |
| --- | --- |
| `Return`, `Abort` | Either bound; neither exit itself diverges. |
| `Step` | Its action and every continuation obey the tree's bound. |
| `bind` | Join of the input and continuation grades. |
| Exception handler | Join of the protected tree and clause grades. |
| `run impl tree` | Join of the tree and implementation-table grades. |

`weaken_grade` permits widening, never narrowing. A terminating request tree
does not imply a terminating interpretation when its implementations or
handler clauses may diverge.

The structural interpreter remains `Tot`: potentially divergent execution
lives in embedded Pulse computations. Two grade-specialized recursive cases
keep the underlying Pulse computation types explicit. Executable Pulse
helpers implement sequencing, framing, returns, and lifting, rather than
extracting calls to semantic-only computation combinators.

| Interpreter | Use |
| --- | --- |
| `run` | Grade-polymorphic F* composition; returns `comp (join g h)`. |
| `run_terminating` | A terminating tree and implementation table; exposes literal `stt` to Pulse. |
| `run_divergent` | A `MayDiverge` tree and implementation table; exposes literal `stt_div`. |
| `run_closed` | A terminating tree with an empty tag type. |
| `run_closed_div` | A tree of either grade with an empty tag type. |

An open interpreter needs implementations for every operation in its
signature. An aborting implementation would return `empty`; normally handlers
eliminate aborts before execution. An unresolved operation is never silently
ignored. An empty signature may have been transformed by framing; it need not
be the particular `Core.empty_ops` function.

## Two-exit rules derived through trees

`Rules.outcome exn a` is `Normal x | Raised e`.
`exit_post q r` selects `q x` or `r e`, so:

```text
stt_exn exn a p q r = stt (outcome exn a) p (fun v -> exit_post q r v)
```

`stt_exn_div` uses `stt_div`. Raising and divergence are independent.
The connection to the reference model is constructive:

```text
of_outcome action = Step action (Normal x -> Return x | Raised e -> Abort Throw e)
observe tree      = handle tree (x -> Return (Normal x)) (e -> Return (Raised e))
run_tree tree     = Core.run_closed (observe tree)
```

`run_tree_div` uses the divergent closing interpreter. The interface exposes
`of_outcome` and `observe` as definitions for arbitrary normal/exceptional
postconditions. The rules construct the corresponding tree transformations
before interpretation, rather than independently proving similar contracts.

| Rules | Meaning |
| --- | --- |
| `return_`, `raise_` | Interpret the selected normal or abortive leaf. |
| `bind`, `bind_div` | Compose through normal leaves only. |
| `frame`, `frame_div` | Preserve a frame on both exits. |
| `lift`, `lift_div` | Embed a nonraising action; exceptional post is `pure False`. |
| `consequence`, `consequence_div` | Ghost steps translate entry ownership and each exit separately. |
| `handle`, `handle_div` | Handle selected payloads; forward others using an entailment under the negated selection predicate. Clauses may re-raise. |
| `with_local`, `with_local_div` | Allocate a scoped Pulse local around interpretation; reclaim its ownership on either outcome. |

`residual r matches e` means `r e ** pure (not (matches e))`. Selection tests
payloads, never satisfiability of spatial assertions.

## Native checker boundary

The checker lowers `raises`, `raise`, and `try ... catch` to two-exit
computations and lexical forward jumps. It does not construct trees at runtime.
The tree derivation supplies the reference proof rules without changing this ABI.

Native contracts retain the transparent alias `Rules.native_outcome exn a`.
The checker recognizes that spelling and splits calls even outside exception
scopes; ignoring a result must not swallow a possible exception. Raw
`Rules.outcome` computations remain ordinary data, including inside native
code. Higher-order native contracts should use `fn ... raises ...`.
Raw semantic callbacks need literal `stt`/`stt_div` types for Pulse readback;
`Native.raw_raise` demonstrates an adapter.

Ordinary calls retain their frame on both exits. Abortive jumps require exact
resource transfer: the destination contract and crossed cleanup scopes must
account for every nonduplicable resource. Exiting a local scope reclaims its
locals; a handler still inside that scope retains access to them.

`try` requires a protected-body `raises` contract. Optional `returns`/`ensures`
annotations cover protected normal completion and catch results. Pattern facts
mask handled payloads; an implicit fallback forwards unmatched ones. Nested
forwarding requires compatible payload types, with no inserted embeddings,
even for an unreachable fallback. The shared extensible `exn` type provides
the conventional common payload type.

Raising is stateful, not ghost or atomic. Clauses run outside their own catch
and may re-raise. Cleanup may contain local catches and loop exits, but cannot
raise, return, break, or jump outside its cleanup boundary and abandon a
pending exit's ownership.

## Build, dependency ordering, and editor support

With the repository's installed stage3 compiler, run here:

```sh
make -j8      # Interfaces and implementations only
make verify
make clean   # This directory's generated artifacts only
```

The example Makefile builds the library before its clients. The bootstrap graph
is `Core.fsti -> Exception.fsti -> Rules.fsti`; each implementation also depends
on its own interface. After these local checked files exist, F* generates the
complete `.depend` graph. This avoids selecting an installed effects cache
instead of the changed sources.

Interface changes invalidate dependent proofs. Implementation-only changes
invalidate extraction without unnecessarily rechecking unchanged client
interfaces. Makefile changes and source-directory membership also participate
in dependency generation. `_cache`, `_output`, and `.depend` are generated.

For fresh proof checking, use `SIL='--force --z3refresh'` and force the desired
make roots with `-W filename` on the `verify` target. Merely rerunning a recipe
can otherwise reuse a root's checked file. `--print_expected_failures` displays
rejection diagnostics. Run example extraction/build targets separately without
`--force`: extraction takes a checked file as its input.

`.fst.config.json` selects the same compiler, local include/cache directories,
`--z3rlimit 10`, and shared dependency/VC settings as make.
`--already_cached` excludes `Pulse.Lib.Effects` here so these sources are checked.
`--warn_error -321` suppresses cache-location warnings, not failed obligations.
Paths are relative to the configuration directory. Restart F* in open editor
buffers after rebuilding dependencies or changing the configuration.

## Current limits

The interpreter establishes its Hoare contract, and constructor types enforce
abortive ownership. The bridge preserves arbitrary two-exit contracts; examples
also fix exact exit values and heap states. There is not yet a full
observational-equivalence theorem for arbitrary opaque callbacks or a
simulation theorem for native lowering.

The trees are well-founded descriptions, not owned first-class resumptions.
Retaining/discarding resumptions, multi-shot handlers, dynamic instances, and
general effect rows need additional design. Divergent callbacks are supported;
an infinite sequence of separately visible requests needs a future delayed
request-generation interface.

The five-case tree executable is supported by Custard specialization, including
literal branch choices at its entry point. `inline_for_extraction` and
`monomorphize` annotations serve this compilation boundary, not the ownership
proof. Arbitrary runtime-shaped existential `Step` trees and native exception
extraction remain separate work.
