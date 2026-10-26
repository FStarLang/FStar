# Resource-indexed effects in Pulse

This directory implements the first review milestone of an extensible effects
library: ordinary Pulse computations embedded in reified control-flow trees,
returning operation implementations, and abortive exception handlers. The goal is
to make control and ownership transfers explicit enough to verify with Pulse's
existing separation logic, without adding a native exception mechanism.

The executable and negative examples are in
[`share/pulse/examples/effects`](../../../../share/pulse/examples/effects/README.md).
Read `Core.fsti`, then `Exception.fsti`, then the examples before studying the
implementation proofs. Names below omit the `Pulse.Lib.Effects.` prefix.

## Files and their responsibilities

| File | Purpose |
| --- | --- |
| [`Pulse.Lib.Effects.Core.fsti`](Pulse.Lib.Effects.Core.fsti) | Operation protocols, the indexed tree, composition/framing/consequence/relabeling, interpreter contracts, and structural request-policy lemmas. Each constructor explains its resource transfer. |
| [`Pulse.Lib.Effects.Core.fst`](Pulse.Lib.Effects.Core.fst) | Executable Pulse helpers, pure tree transformations, the interpreter, and proofs that transformations preserve request policies. |
| [`Pulse.Lib.Effects.Exception.fsti`](Pulse.Lib.Effects.Exception.fsti) | One-layer exception extension, the empty-private-frame discipline, `throw`, abortive `handle`/`catch`, and the theorem needed to compose nested catches. |
| [`Pulse.Lib.Effects.Exception.fst`](Pulse.Lib.Effects.Exception.fst) | Abort-aware sequencing and handler traversals. Shows exactly where the throwing continuation is bypassed and how ownership is accounted for. |
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
instances, automatic unwinding/cleanup, or a recursion interface for arbitrary
effectful loops.

Custard specializes the existential result type stored in `Step`. The executable
examples currently specialize their exception branch choices; their proofs are
uniform in those choices, but arbitrary runtime-shaped trees remain an extraction
limitation. The source-level `inline_for_extraction` and `monomorphize` annotations
serve that extraction boundary, not the logical ownership discipline.
