# Native exceptions in the Pulse compiler

*A reference for F* compiler developers.*

Pulse's native exception support consists of `raises` contracts, `raise`
statements, and `try ... catch` blocks. Checking uses ordinary F* stateful
contracts; execution uses Custard's native exception operations. OCaml and F#
use host exceptions, and Cherry C uses its exception-aware runtime. Standalone
C is rejected: it has no corresponding unwinding support.

The implementation has two central ideas:

1. For verification, a raising function is an ordinary `stt` or `stt_div`
   computation returning a tagged outcome. Its postcondition describes
   ownership on either exit. Lexical forward-jump destinations enforce the
   existing obligations for scopes crossed by an exceptional exit.
2. For extraction, the reserved native outcome type becomes the normal result
   type. Checked raises and handlers become `ERaise` and `ETry`, not executable
   outcome matches or the old flag-based goto lowering.

The checker does not construct or interpret effect trees. The graded effects
library provides a reference model and derives corresponding two-exit rules;
the compiler implements the surface constructs directly.

## 1. Code map and compilation pipeline

Most of the implementation is in the Pulse plugin, not in `src/typechecker`.
The following paths are relative to the repository root.

| Area | Entry points |
| --- | --- |
| Surface syntax and dependency scanning | [`PulseSyntaxExtension.Sugar.fst`](../../pulse/src/syntax_extension/PulseSyntaxExtension.Sugar.fst), [`Grammar.fst`](../../pulse/src/syntax_extension/PulseSyntaxExtension.Grammar.fst) |
| Declaration, lambda, and statement lowering | [`PulseSyntaxExtension.Desugar.fst`](../../pulse/src/syntax_extension/PulseSyntaxExtension.Desugar.fst): `lower_raises`, `wrap_exception_body`, `desugar_stmt'` |
| Checker AST | [`Pulse.Syntax.Base.fsti`](../../pulse/src/checker/Pulse.Syntax.Base.fsti): source `Tm_Raise`, `Tm_ExceptionScope`, `Tm_Try`; checked `Tm_NativeRaise`, `Tm_NativeScope`, `Tm_NativeTry` |
| Exception checking | [`Pulse.Checker.Exceptions.fst`](../../pulse/src/checker/Pulse.Checker.Exceptions.fst): `posts`, `check_scope`, `check_raise`, `unwrap`, `check_try` |
| Stateful call integration | [`Pulse.Checker.ST.fst`](../../pulse/src/checker/Pulse.Checker.ST.fst): `check` |
| Dispatch and payload evaluation | [`Pulse.Checker.fst`](../../pulse/src/checker/Pulse.Checker.fst): `maybe_elaborate_stateful_head`, `check` |
| Lexical exits and cleanup obligations | [`Pulse.Typing.Env.fsti`](../../pulse/src/checker/Pulse.Typing.Env.fsti), [`Pulse.Checker.Goto.fst`](../../pulse/src/checker/Pulse.Checker.Goto.fst), [`Pulse.Checker.Defer.fst`](../../pulse/src/checker/Pulse.Checker.Defer.fst) |
| Result-type convention and reference rules | [`Pulse.Lib.Effects.Rules.fsti`](../../pulse/lib/pulse/lib/effects/Pulse.Lib.Effects.Rules.fsti), [`Rules.fst`](../../pulse/lib/pulse/lib/effects/Pulse.Lib.Effects.Rules.fst) |
| Post-checking transformations | [`Pulse.ElimGoto.fst`](../../pulse/src/checker/Pulse.ElimGoto.fst), [`Pulse.Extract.Main.fst`](../../pulse/src/checker/Pulse.Extract.Main.fst) |
| Runtime ABI | [`Pulse.Lib.NativeExceptions.fst`](../../pulse/lib/common/Pulse.Lib.NativeExceptions.fst), [`FStarC.Custard.Builtins.fst`](../../src/custard/FStarC.Custard.Builtins.fst): `pulse_rule` |

The pipeline is:

```text
Pulse source
  raises annotations  ------> ordinary stt/stt_div outcome contracts
  raise/try/function bodies -> transient exception AST
                                  |
                            Pulse checker
                                  |
                 checked native raise/scope/try
                 + ordinary local/defer/label constructs
                                  |
                    erasure and simplification
                                  |
              native runtime lowering (skip ElimGoto)
                                  |
                     Custard ERaise / ETry
                                  |
                    OCaml / F# / Cherry C
```

Source exception AST nodes must disappear during checking. The separate
checked-native nodes retain runtime control structure only after validating
the two-exit contracts. Non-native functions retain the existing `ElimGoto`
pipeline.

## 2. Two exits, one ordinary computation type

`Pulse.Lib.Effects.Rules` defines:

```fstar
type outcome (exn a:Type0) =
  | Normal : value:a -> outcome exn a
  | Raised : payload:exn -> outcome exn a

type native_outcome (exn a:Type0) = outcome exn a
```

`exit_post q r v` is `q x` when `v = Normal x` and `r e` when
`v = Raised e`. It is marked `pulse_unfold` so the checker can expose the
appropriate spatial assertion after a match.

Schematically, this declaration:

```pulse
fn f (arg:t)
  requires p
  returns x:a
  ensures q x
  raises (fun (e:exn_ty) -> r e)
{ body }
```

has the computation contract:

```text
stt (Rules.native_outcome exn_ty a) p
    (fun v -> Rules.exit_post q r v)
```

For `divergent fn`, replace `stt` with `stt_div`. Raising and divergence are
independent: a terminating function can raise, and catching an exception does
not make a potentially divergent computation terminating.

An exceptional postcondition is an **ownership protocol indexed by the
payload**, not merely an exception set. For example:

```text
r e = pts_to cell (state_of e) ** pure (allowed e)
```

The handler receives this assertion at the throwing state, not the function's
original precondition. `raises (fun _ -> emp)` permits exceptions carrying no
resources. To exclude exceptional completion, use an impossible assertion such
as `pure False`. Dually, `ensures pure False` describes a computation with no
normal completion.

### The `native_outcome` spelling is a compiler contract

Although `native_outcome` is a transparent alias, the checker intentionally
distinguishes its syntactic head from raw `outcome`.
`Exceptions.outcome_types` collects an application and recognizes precisely
the fully qualified `Pulse.Lib.Effects.Rules.native_outcome` head, optionally
universe-instantiated, with two arguments.

This distinction controls call-site elaboration:

| Call result type | Pulse behavior |
| --- | --- |
| `native_outcome exn a` | Automatically split normal and exceptional exits; expose `a` to the ordinary continuation. |
| `outcome exn a` | Leave the result as ordinary data for explicit matching by library clients. |

Recognition is neither a definitional-equality test nor a test of whether an
exception scope is active. Preserving this spelling through type construction
and readback is important; indiscriminately unfolding the alias or recognizing
every raw `outcome` would change control-flow behavior. This is a checker and
extraction ABI convention, not a nominal distinction enforced by F*'s type
system. Use raw `outcome` for explicitly constructed outcome data.

The library's `stt_exn` and `stt_exn_div` aliases use raw `outcome`, deliberately.
For higher-order native callbacks, use `fn ... raises ...` types. Raw semantic
callbacks can instead expose literal `stt`/`stt_div` types for Pulse readback;
the `raw_raise` example supplies such an adapter.

## 3. Parsing and desugaring

The Pulse grammar adds `Raises` annotations and `Raise`/`Try` statements.
`raises` is a Pulse keyword; `raise` is recognized contextually at statement
head, and `catch` is checked as an identifier following a protected block.
They are not globally reserved identifiers that would invalidate qualified
library operations with those names.

### Contracts

`Sugar.outcome_spec` constructs the result type and `exit_post` application
shared by declaration lowering and the grammar's higher-order computation
types. It abstracts the user-written normal result binder into `q`, then
generates a fresh outcome binder. The freshness prevents capture in either
postcondition. The payload type is initially a wildcard, inferred from the
exceptional postcondition.

`Desugar.lower_raises` replaces a native contract's result and postcondition
with this representation, preserving its precondition and any `opens`
annotation. Duplicate `raises` clauses and ghost/atomic contracts are rejected.
Both `comp_to_ast_term` and `desugar_computation_type` use this lowering.

Dependency scanning must also know about generated references: the `Raises`
case of `Sugar.scan_annot` scans a synthetic reference to `native_outcome`,
as well as the user-written exceptional assertion. A file can therefore
depend on `Rules` without explicitly naming it in its source.

### Function bodies and ordinary return

For annotated functions and lambdas, desugaring retains the original normal
contract separately from the outcome contract. `wrap_exception_body` wraps
the body in:

```text
Tm_ExceptionScope {
  normal      = original computation contract, with raises removed;
  exceptional = payload -> slprop;
  body        = ...
}
```

The ordinary `_return` forward-jump block is **inside** this wrapper:

```text
exception scope {
  _return block {
    original function body
  }
}
```

Thus `return x` targets `_return` and remains a normal function exit; the
exception scope subsequently wraps that value in `Normal`. It is not a raise,
and it does not become normal completion of an intervening `try` block.

### Try blocks

A `try` must have an explicit `raises` contract for its protected body.
`returns` and `ensures` are optional; their defaults follow ordinary contract
parsing (`unit` and `emp`). The normal contract applies both to protected
normal completion and to normally returning catch clauses. `requires`,
`preserves`, and `opens` on a `try` are rejected: its entry precondition is the
current context.

Desugaring produces `Tm_Try { normal; exceptional; body; handler }`.
`handler` binds the caught payload at de Bruijn index zero and contains an
ordinary ordered match:

```text
match caught {
  user_pattern_1 -> user_handler_1;
  ...
  _ -> raise caught
}
```

The fallback is always appended. Exhaustiveness comes from proving this
forwarding path unreachable when necessary, not from dropping it.
Try blocks also work as binding initializers.

### AST binding invariants

`Tm_Raise` contains a payload term. `Tm_ExceptionScope` binds no variable in
its source body: the checker creates its label later. `Tm_Try` binds one
payload variable in `handler`, but not in `body`, `normal`, or `exceptional`.

These conventions are reflected in
[`Pulse.Syntax.Naming.fsti`](../../pulse/src/checker/Pulse.Syntax.Naming.fsti)
and [its proofs](../../pulse/src/checker/Pulse.Syntax.Naming.fst),
[`Pulse.Typing.FV.fst`](../../pulse/src/checker/Pulse.Typing.FV.fst),
syntactic equality in
[`Pulse.Syntax.Base.fst`](../../pulse/src/checker/Pulse.Syntax.Base.fst),
and [printing](../../pulse/src/checker/Pulse.Syntax.Printer.fst).
Any AST extension must update these traversals together; in particular,
substitution under the handler shifts by one.

## 4. Checking exception scopes and raises

### Constructing the destination

`Exceptions.posts` checks that the ambient computation is stateful, checks the
exceptional expression against a function type `exn_ty -> slprop`, and requires
both the payload and normal result types to be in `Type0`. It constructs two
post hints: the original normal contract and the outcome contract.

`check_scope` then:

1. Builds the outcome computation using the current precondition.
2. Installs a fresh `_exception` label with `push_exception`.
3. Checks the body against the **normal** post hint.
4. On normal completion, returns `Normal x` against the outcome post hint.
5. Closes the proof scope and emits `Tm_NativeScope` containing the checked
   normal-result body, without the proof-only `Normal` wrapper.

The label contract is constructed by `goto_comp_of_block_comp` in
[`Pulse.Typing.fst`](../../pulse/src/checker/Pulse.Typing.fst). For a block
with postcondition `Q v`, jumping with argument `v` requires `Q v`, and the
jump itself has postcondition `is_unreachable`. For an exception scope,
`Q (Raised e)` reduces to the exceptional ownership protocol.

The verification discipline is schematically:

```text
forward_label L : native_outcome exn_ty a {
  x = check body against normal post, with exception destination L;
  Normal x
}
```

### Raising

Before dispatching a `Tm_Raise`, `Checker.maybe_elaborate_stateful_head`
hoists stateful payload expressions. For example, `raise (!r)` reads the
reference before transferring control. `check_raise` therefore checks a total
payload term, rather than evaluating an arbitrary stateful expression inside
the jump.

`check_raise` finds the nearest exception label, reads its payload/result
types, checks the payload against the required type, and delegates:

```text
raise e  ==>  Goto.check (goto L (Raised e))
```

Concretely, `Goto.check_native_raise` shares `Goto.check`'s payload,
unreachable-post, and exact ownership checks, but returns `Tm_NativeRaise`.
The logical exception label is not an executable goto destination.

There is no search by payload type or constructor. Labels are lexical; no
implicit embedding from one payload type to another is inserted.

With **no** exception destination, `check_raise` requires a proof of
`squash False` and calls `Pulse.Lib.Core.unreachable`. This supports impossible
fallback branches and provably nonraising calls outside exception scopes.
A reachable unhandled raise is a verification failure, not a runtime escape
or a silently discarded outcome.

## 5. Calls, catches, and residual exceptions

### Automatically splitting calls

`Checker.ST.check` first performs ordinary call checking: it reads back the
computation, proves its precondition, resolves arguments, and checks the
application with F*. If the result has the `native_outcome` head, it requires
`C_ST` or `C_STDiv`, adds the caller's remaining frame to the computation,
and invokes `Exceptions.unwrap`.

For a call with postcondition `exit_post q r`, and a caller frame `F`, the
continuations are:

```text
Normal x: q x ** F   -> ordinary continuation with x
Raised e: r e ** F   -> raise e to the nearest lexical destination
```

`unwrap` uses `Checker.Match.check`, substituting `Normal x` into the checked
call's postcondition to construct the normal post hint. It does not erase
payload-dependent facts or restart from the pre-call state.
After checking this split, the runtime term is just the original call result:
the extracted callee returns `a` normally or throws. The proof-only match must
not be executed against the native result, nor may the call be evaluated twice.

The split is unconditional on the existence of an exception scope and on
whether the caller uses the value. In particular, `let _ = f (); ...` and a
semicolon-discarded result cannot swallow an exception. With no destination,
the exceptional branch must prove `False`.

### Catching outside the protected scope

`check_try` first invokes `check_scope` on the protected body, obtaining an
outcome computation. It then matches the result:

```text
Normal x -> return x
Raised e -> handler e
```

Crucially, this match is checked **outside** the new exception label. A catch
clause that raises again targets the enclosing exception destination, not
itself. It may change the state or translate the payload, provided it
establishes the outer exceptional contract.

The checked runtime `Tm_NativeTry` keeps the protected normal-result body and
the checked `Raised` branch. Substituting `Raised payload` into the checked
match selects that branch during Custard simplification; it does not allocate
an outcome at runtime.

The payload match generated by desugaring uses the ordinary match checker's
ordered-pattern facts. In
[`Pulse.Checker.Match.fst`](../../pulse/src/checker/Pulse.Checker.Match.fst),
`push_not_matches_hyps` records that each earlier pattern failed; the branch
also gets its own pattern equality. Thus the fallback receives, logically:

```text
r e ** pure (e matches none of the preceding patterns)
```

This is the native counterpart of `Rules.residual`. There is no operation
testing satisfiability of an `slprop`: handler selection tests payloads.
The branch facts either justify forwarding to an outer contract or prove the
fallback impossible.

For example, after catching `First`, forwarding may establish
`failed r e ** pure (e == Second)` from a closed two-constructor payload
type. With extensible `exn`, failure to match one constructor instead gives
an exclusion fact; it does not enumerate every remaining constructor.

Forwarding still typechecks the original payload against the outer
destination's type, even on an impossible fallback. Nested payload types must
therefore be compatible; dead-code reasoning does not synthesize a sum
injection or exception translation.

## 6. Ownership, locals, and cleanup

This is the main difference from simply adding an error-result datatype.
An abortive exit has no continuation in which to retain a private frame.

### Calls may frame; jumps must account for the frame

An ordinary call can preserve unrelated ownership around both outcomes.
Once its `Raised` branch jumps, however, that ownership must be transferred
to the destination, consumed by crossed cleanup, or otherwise discharged.

`Checker.Goto.check'` uses `Prover.prove_exact`, not ordinary precondition
framing. `prove_exact` proves the destination obligation and then calls
`check_remaining` on the leftover context. Unconsumed nonduplicable resources
cause an error. Duplicable assertions may remain, and an unreachable context
is treated specially; "exact" does not mean syntactic equality of assertions.

For example, if the caller owns `cell |-> 0 ** other |-> 17` and a callee
raises with `cell |-> 1`, propagating to an outer contract mentioning only
`cell |-> 1` is invalid. The `other` resource is still owned. Put it in the
outer protocol, reclaim it, or handle the exception within its scope.

This exact-transfer check applies to **all gotos**, including ordinary
`return`, `break`, and `continue`. Otherwise an early return inside a `try`
could abandon resources by bypassing an impossible protected continuation.

### Lexical cleanup obligations

The environment represents an exception destination as an ordinary
`BindingGotoLabel` with `is_exception = true`. `exception_label` selects the
nearest such binding. Separately, `lookup_goto` accumulates `BindingPost`
assertions between the jump site and its destination.

[`Checker.WithLocal`](../../pulse/src/checker/Pulse.Checker.WithLocal.fst)
and [`Checker.WithLocalArray`](../../pulse/src/checker/Pulse.Checker.WithLocalArray.fst)
push these assertions when entering local scopes. A jump crossing the scope
must provide the permission needed to reclaim the local, in addition to the
destination's ownership protocol. For references this uses `pts_to_uninit`:
the final value need not be known, but reclamation still needs ownership.

Lexical placement determines whether a local is reclaimed. A handler inside
the local's scope sees the local alive; a jump to a handler outside crosses
its reclamation obligation. Exporting half of a local's permission cannot
also satisfy the obligation to reclaim the whole local.

### Defer cannot replace a pending exit

`Checker.Defer.check` pushes the cleanup precondition as another `BindingPost`
while checking the protected body. On normal completion, the body must also
return that assertion. The cleanup itself is checked from its precondition
to `emp`, with the pending exit's ownership kept out of its working context.

While checking cleanup, the environment contains `BindingCleanupBoundary`.
Both `exception_label` and `lookup_goto` stop there. A cleanup may create and
use its own local catches or loop exits, but cannot raise, return, break, or
jump to a destination outside the boundary. An automatically split native
call is subject to the same restriction.

Without this boundary, a replacement exception or return could abandon the
resources reserved for the pending exit. Supporting escaping cleanup would
require a different ownership rule, not just relaxing label lookup.

### Functions cannot capture exits

[`Checker.Abs.check_abs_core`](../../pulse/src/checker/Pulse.Checker.Abs.fst)
uses `clear_goto` before checking an abstraction's body. This keeps variable
bindings but removes labels and cleanup bookkeeping. A local function must
have its own native contract; it cannot capture and jump to its defining
function's exception destination. Its caller subsequently propagates the
outcome through the usual call rule.

## 7. Extensible F* exceptions

Native payloads can be numbers, closed datatypes, or the shared F* `exn` type.
The native checker does not require `exn` specifically.

```fstar
exception BadRequest of nat
exception ConnectionLost of string
```

These declarations use the existing F* front end:
[`FStarC.ToSyntax.ToSyntax.fst`](../../src/tosyntax/FStarC.ToSyntax.ToSyntax.fst)
handles `Exception` by emitting a constructor of `exn`, qualified
`ExceptionConstructor`, without generated projector/discriminator declarations.
Use explicit matches rather than expecting closed-datatype `C?` helpers.

Using `exn -> slprop` at each native boundary gives nested scopes a common
payload type without inserted embeddings. Constructors retain their identity:
two exception constructors carrying `nat` are not interchangeable. An
additional constructor declared later can pass through an existing selective
handler.

This reuses exception **values**, not host-language exception control flow.
Listing all constructors currently used by a client is not an exhaustive
match for arbitrary `exn`; only its exceptional contract can rule out the
implicit forwarding branch.

## 8. Relationship to the graded effects library

The canonical model is
[`Pulse.Lib.Effects.Core`](../../pulse/lib/pulse/lib/effects/Pulse.Lib.Effects.Core.fsti),
with the exception layer in
[`Pulse.Lib.Effects.Exception`](../../pulse/lib/pulse/lib/effects/Pulse.Lib.Effects.Exception.fsti).
There is no separate native tree interpreter.

`Core.tree ops grade a pre post` distinguishes returning operations from
aborting operations. `Perform` has a continuation and can retain a private
frame. `Abort` has neither: its precondition is exactly the operation's
request protocol. The exception layer adds an aborting `Throw` operation
whose request is the exceptional postcondition.

Framing a tree strengthens **every abortive protocol**, including outer
exception layers. Otherwise a raise could strand ownership in a continuation
that never resumes. `Terminating` and `MayDiverge` grades select `stt` and
`stt_div`; composition and interpretation join the relevant bounds.

`Rules` connects ordinary two-exit computations to this model:

```text
of_outcome action =
  Step action (Normal x -> Return x | Raised e -> Abort Throw e)

observe tree =
  handle tree (x -> Return (Normal x)) (e -> Return (Raised e))

run_tree tree = Core.run_closed (observe tree)
```

`run_tree_div` uses the divergent interpreter. The implementations of
`return_`, `raise_`, `bind`, `frame`, `consequence`, and `handle` construct
these tree transformations and run the common interpreter. `with_local`
places ordinary Pulse local allocation around interpretation and reclaims
the local on either outcome.

These are derived library rules, not additional assumed logical control
operators. However, the native checker does **not** elaborate to calls to
these combinators: it emits matches and lexical control flow using existing
Pulse checking infrastructure. The library derivation and the native checker
share the two-exit contracts and ownership discipline. They are not yet
connected by a general simulation theorem for native lowering, nor is there
a full observational-equivalence theorem for arbitrary opaque callbacks.

## 9. Native extraction and current limits

`Pulse.Extract.Main.extract_pulse_dv` detects checked native constructs and
native-call binders **before** simplification. This includes fully handled
exceptions, nested functions, and scopes whose exceptional postcondition is
`False`. Such functions bypass `Pulse.ElimGoto`: the older conditionalized
label lowering could lose early-return values or overwrite a non-unit defer
result with cleanup's unit value.

### Result and exception representations

Custard's `pulse_rule` maps `Rules.native_outcome exn a` to runtime `a`.
Ordinary `Rules.outcome` remains an ordinary datatype; the tree interpreter's
ABI is unchanged. Native function arguments, recursive calls, and callbacks
must consistently use this reserved native ABI.

`Tm_NativeRaise` boxes its checked payload with `FStar.Dyn.mkdyn` and raises
`Pulse.Lib.NativeExceptions.NativeException`. `Tm_NativeTry` catches exactly
this wrapper and unboxes at its checked payload type with `FStar.Dyn.undyn`.
This works for integers, booleans, and user-extensible `exn` values alike.
Source catch patterns still operate on the original payload. Even a payload
whose type is `exn` is wrapped; it cannot impersonate a compiler control exit.

The reflection terms use `FStar.All.raise` and `try_with`, whose existing
Custard rules produce `ERaise` and `ETry`. OCaml and F# print host-language
exceptions. Cherry handles propagation, managed payload ownership, and
exception-aware unwinding through its existing runtime. Standalone C rejects
the native ABI and exception operations instead of silently changing their
semantics.

Separate compilation must preserve the identity of the runtime wrapper, not
redeclare it in each OCaml module. `PrintOCaml.build_tables` qualifies imported
`DExn` constructors just like imported variant constructors. Unsplit unit
exports keep their fully mangled exception names: choosing a short name from
the consumer's set of constructors would make the ABI depend on unrelated
client declarations. The `.cui` format version rejects artifacts from before
this naming convention. Cherry identifies exception and dynamic-type
descriptors by name across separately compiled translation units.

### Ordinary returns, breaks, and cleanup

Native-containing functions still have lexical forward labels for ordinary
returns and loop exits. Each label becomes a local callable that stores its
result in a scoped `option a` reference and throws `ControlFlow key`. The
label's enclosing handler catches only that module-qualified label key and
reads the stored result. Initializing the slot to `None` avoids uninitialized
managed values in Cherry. Each recursive activation catches its own exit;
the checker forbids capturing labels across function boundaries.

Cherry's reference-counting pass also tracks pending cleanup for Pulse stack
buffers. Their pointers are borrowed, but their cells own managed values:
dropping ordinary owned variables alone would leak the cells on an exception.
`exn_exit` empties these buffers in innermost-first order before leaving the
function. Initializer evaluation precedes registration of that cleanup.

The control channel is distinct from `NativeException`: a source catch-all
must not intercept `return`, `break`, or `continue`. Foreign host exceptions
also pass through source catches unchanged.

A checked `defer` carries its body's result type. Extraction preserves it as:

```text
let result =
  try body
  with pending -> cleanup; raise pending
in cleanup; result
```

Thus cleanup runs on normal completion, a Pulse raise, or a lexical control
exit, and never replaces the body's result. Normal cleanup is outside the
protected expression so a cleanup failure cannot run the same cleanup twice.
Nested local handlers in cleanup use the same native exception machinery.

The eraser, simplifier, and extractor traverse checked-native nodes but
reject residual source `Tm_Raise`, `Tm_ExceptionScope`, or `Tm_Try` as internal
errors. `ElimGoto` rejects checked-native nodes as well: routing one through
the non-native pipeline is a compiler error.

`pulse.noextract` cannot bypass the native runtime lowering: for native
definitions it records an `extraction_error` attribute. Custard also checks
that attribute when loading checked files, rather than extracting the opaque
verification body.

Other current boundaries are deliberate: stateful computations only,
`Type0` payloads/results, explicit protected-body exceptional contracts, no
automatic payload embeddings, and no nonlocal exits from cleanup. This is
abortive exception handling, not general resumable effects, dynamic effect
instances, or inferred effect rows.

## 10. Regression scenarios and maintenance checklist

The primary native suites are
[`Example.Effects.Native.fst`](../../pulse/share/pulse/examples/effects/Example.Effects.Native.fst)
and
[`Example.Effects.NativeRejected.fst`](../../pulse/share/pulse/examples/effects/Example.Effects.NativeRejected.fst).
The [scenario guide](../../pulse/share/pulse/examples/effects/README.md)
describes their exact contracts.
[`Example.Effects.NativeRuntime.fst`](../../pulse/share/pulse/examples/effects/Example.Effects.NativeRuntime.fst)
and its OCaml, F#, and Cherry drivers execute native exception regressions.
This is separate from the five-case tree-interpreter runtime demonstration.
`NativeStress` adds driver-observed LIFO cleanup on normal, raise, return,
break, and continue paths, 257-frame unwinding, and 1,000 repeated exceptions.
`NativeBoundary.fsti`/`.fst` exercise a polymorphic native ABI and callbacks
capturing managed payloads and owned state, including real separate Custard
compilation for OCaml and Cherry. The driver-private observer does not require
discarding Pulse permissions or adding axioms.

| Invariant | Representative definitions |
| --- | --- |
| Precise normal and exceptional facts; call splitting | `maybe_value`, `increment_result`, `known_normal`; rejection: `ignored_exception` |
| Partial handling and outward re-raising | `partial`, `reraised`, `translate`; rejections: `unmatched`, `unhandled_reraise` |
| Ownership survives an abort | `framed_call`; rejections: `lost_frame`, `reraise_abandons_resource`, `return_abandons_frame` |
| Scope-sensitive local reclamation | `update_and_raise`, `handler_inside_scope`; rejection: `escaped_local_permission` |
| Cleanup may handle locally but not escape | `deferred_free`, `cleanup_handles_locally`, `cleanup_local_loop`; rejections: `escaping_cleanup`, `cleanup_call_escapes`, `cleanup_return_abandons_exception` |
| Function boundaries and higher-order contracts | `invoke`, `locally_defined`, `countdown`; rejection: `captured_exception_exit` |
| Outcome data is not automatically a control effect | `raw_raise`, `raw_outcome` |
| Raising is not divergence or a ghost effect | `maybe_value`; rejections: `catch_is_not_termination`, `ghost_raise`, `atomic_raise` |
| Stateful payloads, loops, and ordinary return | `raise_read`, `loop_exit`, `skipped_write`, `early_return` |
| Open exception identity and residual forwarding | `exn_nested`, `exn_reraised`, `exn_later_extension`; rejection: `exn_known_cases_are_not_exhaustive` |

The rejected suite uses `expect_failure`; its declarations must fail at the
intended proof/checking boundary, not merely fail later during extraction.
The library's `Example.Effects.Rules`, `Graded`, and `Rejected` suites cover
the derived rules and semantic ownership/grade constraints separately.

After rebuilding the compiler/plugin, the example directory's `make verify`
builds the effects library and verifies the examples without requesting
runtime extraction. To force the native roots rather than reuse their
checked files, the existing rules support:

```sh
make -C pulse/share/pulse/examples/effects \
  SIL='--force --z3refresh' \
  -W Example.Effects.Native.fst \
  -W Example.Effects.NativeRejected.fst verify
```

`make CHERRY_CC=gcc-15 native-ocaml native-fsharp native-cherry native-separate`
in the effects directory runs the native executable checks; Cherry runs
distinct `-O0` and `-O2` binaries with address/undefined-behavior sanitizers,
leak detection, and strict warnings. `make check-native-extraction` checks
standalone-C refusal from source and checked files, with raw outcomes as a
positive control. It also checks that `pulse.noextract` cannot bypass the
native lowering, from either source or a persisted checked file.

For changes to this implementation, preserve the `native_outcome` recognition
boundary, the handler's binding depth, unconditional splitting of native
calls, exact ownership transfer at jumps, and lexical cleanup/function
boundaries. Check these invariants before attributing a failure to SMT:
each determines which control paths and resources the proof actually sees.
