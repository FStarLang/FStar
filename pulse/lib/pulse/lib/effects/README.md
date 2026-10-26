# Resource-indexed effects in Pulse

This directory contains two complementary developments in Pulse's existing
separation logic: reified control-flow trees for extensible operations, and
two-exit proof rules underlying the native exception checker. Both make control
and ownership transfers explicit; neither adds an assumed logical effect rule.

The executable and negative examples are in
[`share/pulse/examples/effects`](../../../../share/pulse/examples/effects/README.md).
Read `Core.fsti`, then `Exception.fsti`, then the examples before studying the
implementation proofs. For native syntax, read `Rules.fsti` and
`Example.Effects.Native.fst` instead. Names below omit the
`Pulse.Lib.Effects.` prefix.

## Files and their responsibilities

| File | Purpose |
| --- | --- |
| [`Pulse.Lib.Effects.Core.fsti`](Pulse.Lib.Effects.Core.fsti) | Operation protocols, the indexed tree, composition/framing/consequence/relabeling, interpreter contracts, and structural request-policy lemmas. Each constructor explains its resource transfer. |
| [`Pulse.Lib.Effects.Core.fst`](Pulse.Lib.Effects.Core.fst) | Executable Pulse helpers, pure tree transformations, the interpreter, and proofs that transformations preserve request policies. |
| [`Pulse.Lib.Effects.Exception.fsti`](Pulse.Lib.Effects.Exception.fsti) | One-layer exception extension, the empty-private-frame discipline, `throw`, abortive `handle`/`catch`, and the theorem needed to compose nested catches. |
| [`Pulse.Lib.Effects.Exception.fst`](Pulse.Lib.Effects.Exception.fst) | Abort-aware sequencing and handler traversals. Shows exactly where the throwing continuation is bypassed and how ownership is accounted for. |
| [`Pulse.Lib.Effects.Rules.fsti`](Pulse.Lib.Effects.Rules.fsti) | Two-exit computation contracts, return/raise, sequencing, framing, consequence, partial handling, and local reclamation; also the native checker's result-type convention. |
| [`Pulse.Lib.Effects.Rules.fst`](Pulse.Lib.Effects.Rules.fst) | Derives the two-exit rules with ordinary Pulse operations, for both terminating and potentially divergent computations. No tree interpreter or native raise is used in these proofs. |
| [`Makefile`](Makefile) | Independent, incremental verification of these interfaces and implementations, using a local cache rather than trusting installed copies of the development. |
| [`.fst.config.json`](.fst.config.json) | VS Code compiler, checking options, and include paths; its fields are described below because JSON does not support inline comments. |
| `README.md` | This file: the semantic overview, reading map, build contract, editor setup, and limits of the milestone. |

Generated `.depend`, `_cache/`, and `_output/` contents are build artifacts, not
additional library definitions. They should not be edited or treated as the
authoritative source of a specification.

## What a program owns, and when

`Core.prog ops a p q` is a description of a computation whose execution starts
with ownership `p` and returns an `a` satisfying `q`. Constructing or duplicating
the description does not allocate, consume, or duplicate the resources described
by `p`. The interpreter still needs that ownership to execute it.

The three constructors express different boundaries:

| Constructor | Meaning |
| --- | --- |
| `Return x` | Return immediately; the entry resources already satisfy `q x`. |
| `Step action next` | Delay an ordinary Pulse action. Its result `x` and postcondition `s x` feed `next x`. |
| `Perform op arg next` | Give the operation `request arg`; retain a private `frame`; resume with a reply value `y` and `reply arg y ** frame`. |

Thus an operation may change ownership, not just return data:

```text
at request:       request arg ** frame
operation owns:   request arg
on resumption:    reply arg y ** frame
```

The old request assertion is not automatically available after resumption.
`Example.Effects.Core` makes this concrete with an exchange operation whose
request owns a reference at 0 and whose reply owns it at 1.

`bind` threads postconditions into continuations. `frame` carries extra ownership
through the tree without passing it to operation implementations. `consequence`
uses ghost entailments to change the exposed pre/postconditions. `weaken` relabels
requests while requiring equality of their protocols; it is not a theorem about
preserving nominal identity, since the embedding need not be injective.

`run` interprets the tree using returning implementations of all its operations.
`run_closed` needs no implementation table because its tag type is empty.
Handling and forwarding eliminate or relocate effects before this closing step;
an unresolved effect is not silently ignored.

## Why abortive handling needs another ownership rule

An exception uses `output = Core.empty`: no reply value can resume its
continuation. Nevertheless, that continuation's private resources must still be
accounted for. Discarding code is not permission to discard ownership.

Both `Exception.handle` and `Exception.catch` remove one local exception layer,
invoke a normal or exceptional clause, and forward `Other` operations. Neither
lets the clause resume the throwing continuation. Their distinction is:

| API | Input discipline | Exceptional clause owns |
| --- | --- | --- |
| `handle` | Unrestricted `Core.prog` in the extended environment | `exceptional e ** frame`, for every possible private frame |
| `catch` | `Exception.prog`, a refinement requiring empty private frames at local throws | `exceptional e` |

The universal frame parameter makes `handle` a low-level, resource-explicit API:
its clause must account for arbitrary ownership while establishing a fixed
result postcondition. It is not automatically implementable from an ordinary
exception-only clause. `catch` uses the tree's refinement to prove the frame is
`emp` at each local throw and therefore exposes the simpler clause type.

For example, if recovery must update a reference, include that reference's
ownership in `exceptional e`. Putting it only in a throw's private frame will
not satisfy `Exception.prog`. Likewise, applying `Core.frame` to an open throwing
tree generally breaks this refinement. Framing the already handled computation
is different: the surrounding Pulse computation retains the additional resource
while executing a closed handler result.

`all_requests` expresses these disciplines structurally, over all continuation
arguments. A local frame policy says nothing about `Other` requests.
`forwarded_policy` and `catch_all_requests` carry an enclosing layer's policy
through an inner handler, including the requests introduced by its clauses.
The nested example exercises this distinction explicitly.

## Two-exit rules and the native checker

`Rules.outcome exn a` has constructors `Normal x` and `Raised e`.
`Rules.exit_post q r` selects `q x` or `r e`. Thus:

```text
stt_exn exn a p q r =
  stt (outcome exn a) p (fun v -> exit_post q r v)
```

`stt_exn_div` uses `stt_div` instead. The `_div` rules have the same
ownership discipline as their terminating counterparts; divergence is
independent of the possibility of raising.

| Rule | Ownership and control obligation |
| --- | --- |
| `return_`, `raise_` | Establish precisely the selected exit's resources. |
| `bind`, `bind_div` | Run the continuation only on normal return; share the exceptional contract between both computations. |
| `frame`, `frame_div` | Preserve the frame on **both** exits. |
| `lift`, `lift_div` | Embed a nonraising action with exceptional post `pure False`. |
| `consequence`, `consequence_div` | Prove separate precondition, normal-exit, and exceptional-exit entailments. |
| `handle`, `handle_div` | Handle selected payloads; prove forwarding under the negation of the selection predicate. Both clauses may themselves raise under the outer contract. |
| `residual` | Express the unhandled domain as `r e ** pure (not (matches e))`, not as a decision procedure for satisfiability of `r e`. |
| `with_local`, `with_local_div` | Reclaim full local ownership on either exit; expose neither its permission nor its cleanup obligation in the public postconditions. |

The native checker lowers `raises`, `raise`, and `try ... catch` to this
two-exit representation plus existing lexical forward jumps. It does not
construct or interpret `Core.prog` trees. The function's normal return label is
inside its exception scope. A catch clause is outside the scope it handles, so
re-raising reaches an outer handler rather than the same catch again.

Calls are split into their two exits, with their ordinary frame present on
both. Abortive jumps require exact resource transfer: their destination
contract and the cleanup obligations of crossed scopes must account for every
nonduplicable resource. Ordinary call framing is insufficient at a jump,
because its continuation will not run. Scoped locals use the existing cleanup
machinery; a handler still inside a local's scope retains that local.

### Representation boundary

Native contracts retain the transparent alias `Rules.native_outcome exn a`
as their result type in ordinary `stt`/`stt_div` computations. The checker
recognizes that spelling to split native calls even outside an exception scope:
ignoring a returned value must not silently swallow an exception. Raw
`Rules.outcome` computations remain ordinary data for library proofs, including
when called from native code.

This alias is an internal ABI convention, not a new logical computation
constructor or a nominal effect distinction. Hand-written native higher-order
types should use `fn ... raises ...`, preserving the convention, rather than
unfolding the alias or presenting the computation through a raw outcome type.
The current readback also needs literal `stt`/`stt_div` types for raw semantic
callbacks; the proofs spell those out instead of relying on recognition of
`stt_exn` aliases. `Native.raw_raise` shows the same adapter for clients.

### Current native slice

`try` requires an explicit protected-body `raises` contract. Optional
`returns`/`ensures` annotations describe both its protected normal completion
and its catch results; the entry context supplies its precondition. The
checker uses ordinary match-pattern facts to mask handled payloads, with an
implicit unmatched forwarding branch. Nested forwarding scopes use compatible
payload types; this slice does not insert payload embeddings between different
types, including in an implicit unreachable fallback.

Payloads and results are in `Type0`. Raising is permitted only in stateful
computations, not ghost or atomic computations. No new open-invariant rule is
needed. Ordinary catches may re-raise or raise a different payload. A `defer`
cleanup may catch exceptions and use local control flow internally, but may not
raise, return, break, or jump to a destination outside the cleanup: the existing
normal-only cleanup rule does not justify abandoning a pending exit's resources.

Native Custard extraction, resumable handlers, dynamic instances, and general
effect rows are separate work. These examples establish checking and proof
rules, not an efficient native runtime or a mechanized simulation theorem for
the new lowering.

## Building and incrementality

With the repository's installed stage3 compiler available, run from this directory:

```sh
make -j8
make verify
make clean
```

Default `make` verifies the library; it does not extract a standalone polymorphic
library executable. The examples' Makefile builds this library automatically
before verifying or extracting its clients.

The bootstrap ordering is:

```text
Core.fsti -> Core.fst
Core.fsti -> Exception.fsti -> Exception.fst
Rules.fsti -> Rules.fst
```

The Makefile first materializes local checked outputs, then asks F* to generate
the complete `.depend` graph. This avoids accidentally selecting an installed
effects cache as the target to update. The explicit cross-interface bootstrap
edge must be maintained if more library interfaces are introduced.

An implementation-only change updates its checked implementation without
rechecking clients of an unchanged interface. The examples additionally depend
on checked implementations for extraction, so such a change still reaches their
executable. Interface changes invalidate their dependent proofs. The local
Makefile and source-directory membership also participate in dependency
generation. `clean` removes only this directory's generated artifacts.

## Editor configuration: `.fst.config.json`

The F* VS Code extension selects the nearest configuration in the workspace
hierarchy and, for this configuration, uses its directory as the working
directory. All paths are relative to that directory, not an absolute developer
checkout location.

| Field or option | Why it is present |
| --- | --- |
| `fstar_exe` | `../../../../../stage3/out/bin/fstar.exe` selects the same installed compiler family as the Makefile, with Pulse support available. |
| `include_dirs` | `.` finds these sources; `_cache` exposes this development's checked modules instead of relying on installed effects copies. |
| `--cache_dir _cache` | Uses the local checked cache. Run `make` to populate or refresh it; opening a file is not a replacement for building all dependencies. |
| `--already_cached ...` | Reuses installed F*/Pulse prerequisites. The final `-Pulse.Lib.Effects` excludes this development from that blanket assumption. |
| `--z3rlimit 10` | Matches the proof budget used by the Makefile. |
| `--warn_error -321` | Matches the build's suppression of warnings about checked files found at an unexpected location; it does not admit failed proof obligations. |
| `--ext optimize_let_vc` | Matches the build's Pulse verification-condition optimization setting. |
| `--ext fly_deps` | Matches the build's dependency-loading setting. |

After changing the configuration or rebuilding dependencies, use **F*: Restart**
in an already-open document to start a fresh session. The examples have their own
configuration, including this library's source and cache directories.

## What this milestone does not claim

The interpreter's type establishes its advertised Hoare contract; the policy
lemmas establish compositional ownership restrictions. There is no separate
observational-equivalence proof or complete algebraic-law development yet.

These trees are not owned, first-class stack resumptions. The library does not
provide multi-shot continuations, a general resumable handler API, dynamic effect
instances, or a recursion interface for arbitrary tree-based effectful loops.
Native exceptions separately support scoped cleanup, recursive calls, and
exceptional exits from loops as described above.

Custard specializes the existential result type stored in `Step`. The executable
examples currently specialize their exception branch choices; their proofs are
uniform in those choices, but arbitrary runtime-shaped trees remain an extraction
limitation. The source-level `inline_for_extraction` and `monomorphize` annotations
serve that extraction boundary, not the logical ownership discipline.
