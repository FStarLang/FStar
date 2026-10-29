# Effects examples: what is verified and what is executed

This directory exercises the resource-indexed effects library in
[`lib/pulse/lib/effects`](../../../../lib/pulse/lib/effects/README.md).
All library examples use the single graded model in `Pulse.Lib.Effects.Core`
and its `Exception` layer. `Rules` exercises the two-exit rules derived through
that interpreter. Negative examples check invalid ownership and grade uses.
`Native` and `NativeRejected` separately exercise the native two-exit checker,
without constructing effect trees. Their Custard extraction is deferred.

Start with `Core`, `Exception`, and `Nested`, then `Graded` and `Rules`.

## File map

| File | What to look for |
| --- | --- |
| [`Example.Effects.Core.fst`](Example.Effects.Core.fst) | Delayed heap actions, an operation with a state-changing request/reply contract, explicit tree framing, an erased old-state witness, consequence, and forwarding through an exception layer that cannot throw. |
| [`Example.Effects.Exception.fst`](Example.Effects.Exception.fst) | A throwing branch and a normal branch, exact recovery ownership, unreachable continuation code, and framing around the handled result. |
| [`Example.Effects.Nested.fst`](Example.Effects.Nested.fst) | Two unit-payload exception layers distinguished by tags. Ordinary handlers compose without policy proofs, changing the result type from empty to int to bool. |
| [`Example.Effects.Graded.fst`](Example.Effects.Graded.fst) | Nested handling of an open framed tree, returning-operation framing, divergent actions/implementations/clauses, mixed-grade bind, and exact outcome round trips. Verification only. |
| [`Example.Effects.Rules.fst`](Example.Effects.Rules.fst) | Tree-derived two-exit bind, frame, partial handling and re-raising, local reclamation on both exits, and divergent callbacks. Verification only. |
| [`Example.Effects.Rejected.fst`](Example.Effects.Rejected.fst) | Twelve expected failures covering ownership, operation kinds, unresolved effects, framing, and grades. Not an executable test module. |
| [`Example.Effects.Native.fst`](Example.Effects.Native.fst) | Native raises contracts, partial catches, re-raising, exact state transfers, framing, local reclamation, cleanup, loops, recursion, and higher-order calls. Verification only. |
| [`Example.Effects.NativeRejected.fst`](Example.Effects.NativeRejected.fst) | Expected rejections for lost ownership, unhandled calls, incomplete handlers, escaping cleanup, invalid local reclamation, and ghost/atomic raises. Verification only. |
| [`Example.Effects.Runtime.fst`](Example.Effects.Runtime.fst) | The one extraction entry point. Calls five concrete cases and returns a list of runtime comparisons, with a proof that they are all true. |
| [`driver.ml`](driver.ml) | External OCaml harness that checks the complete list returned by the extracted entry point and fails the executable if any observation differs. |
| [`Makefile`](Makefile) | Builds the library first, verifies all examples, extracts the runtime entry, links the driver, and records a successful run incrementally. |
| [`.fst.config.json`](.fst.config.json) | VS Code compiler/options/include configuration. It includes both source and cache directories of the library; see the field descriptions below. |
| `README.md` | This scenario guide, expected observations, build-stage descriptions, and editor setup. |

The original sketch `../Effects.fst` is outside this directory and is not part
of this suite. Generated `.depend`, `_cache/`, and `_output/` files are not
additional authored examples and should not be edited.

## The five executable observations

`Runtime.test` returns five booleans in the following fixed order.

| Case | Observed value | What it exercises |
| --- | --- | --- |
| `Core.test ()` | `(0, 42, 2, 7)` | Tree construction leaves the initial cell untouched; execution forwards an exchange request, returns 42, finishes at state 2, and preserves a framed cell at 7. |
| `Exception.test true` | `(42, 2)` | The throwing branch transfers ownership at state 1 to recovery, which writes 2 and returns 42. |
| `Exception.test false` | `(7, 3)` | Normal completion writes 3 and returns 7 through the normal clause, without exceptional recovery. |
| `Nested.test true` | `(true, 2)` | The inner exception is caught; its result is passed to the outer normal clause and translated to true. |
| `Nested.test false` | `(false, 3)` | The outer exception is forwarded through the inner handler and caught by the outer exceptional clause. |

These are exact result/state specifications, not just type-safety checks. The
driver also evaluates the comparisons in extracted code; it requires exactly
`[true; true; true; true; true]` before printing success.

The exception and nested test flags are marked `monomorphize`. Their proofs
cover either flag value, while `Runtime.test` supplies literal flags so Custard
can specialize the tree shapes. This suite does not demonstrate arbitrary
runtime-dependent exception-tree shape extraction.

## Ownership and control scenarios

### Graded intrinsic trees

`Graded.nested_frame b` follows the same routes as `Nested.test`,
but frames the **open** computation with a second cell initially at 1.
Both local and outer exceptions acquire that cell in their protocols.
The result is exactly `(b, (2, 2))` when `b`, and `(b, (3, 3))` otherwise:
either handler receives and updates both cells. The one `framed_layer` call
exposes the framed outer signature without a separate ownership proof.

`Graded.returning_frame ()` returns `(10, (1, 5))`. The returning operation updates
only its request cell; the private framed cell stays at 5 while the request is
forwarded through an exception handler.
`mixed_steps` joins a terminating prefix with a potentially divergent action.
`divergent_implementation` and `divergent_handler` start from terminating request
trees but produce potentially divergent interpretations or handled trees.
Their recursive callback genuinely loops when requested, rather than merely
being an ordinary action annotated as divergent.

`Graded.outcome_round_trip b` returns exactly `(b, (10, 1))` or
`(b, (7, 1))`. It embeds an arbitrary-style two-exit callback, handles its
exception into data, and interprets the result; both its outcome and heap
update survive the bridge.

`Rules.bind_frame_reraise b` returns `(20, (2, 5))` on the normal route.
On the exceptional route it skips the bind continuation, lets the handler
update the framed cell, and re-raises: the result is `(8, (3, 6))`.
`with_local` preserves the callback's exact two-exit contract while reclaiming
the local on either route. `divergent_program` checks the same bind/frame/handler
composition for a genuinely recursive callback.

`Graded` and `Rules` are proof examples, not extraction entry points.
The five-case executable uses the same canonical model; native Custard extraction
and arbitrary delayed request generation are separate milestones.

### Core operations

`ops r` describes an exchange over a particular reference. Its input contains
an erased old-state witness and a runtime new value. The reply returns the old
integer together with ownership at the new state, making both the returned data
and the state transition available to the continuation's proof.

`client` composes the read, exchange, and final update. `through_handler` embeds
the operations under an uninhabited exception layer and removes that layer again;
its requests must still reach the original exchange implementation. `test`
combines that forwarding with explicit `Core.frame`.

`framed` is a smaller, separately verified framing helper. `positive_client`
and its ghost helpers exercise consequence by weakening result 42 to a positive
result without losing reference ownership. They are not additional runtime
entry-point calls.

### Local exception recovery

`exceptional` owns the cell at 1, before the exception clause runs. `normal`
describes an ordinary body return at state 3 with result 7. `handled` combines
the two routes into an exact flag-indexed final contract.

`body` sequences a deliberately impossible `dead_write` after `throw`. Its
precondition contains `pure False`; verification of that helper does not make it
reachable. The exception operation has no reply value, and abortive sequencing
bypasses the continuation. Recovery instead uses the ownership transferred in
the exceptional protocol to write 2.

`framed_test` verifies that an unrelated cell at 17 can remain outside the
exception protocol when framing execution of the already handled computation.
It does not frame an open throwing tree, and it is not called by `Runtime.test`.

### Nested routing

The two layers both use unit payloads. An inner request uses `Throw`; an outer
request, seen from the inner environment, uses `Other Throw`. This tests static
layer identity independently of payload type.

`body` prepares the selected request's ownership and constructs an `Abort`.
`handle_inner` removes the local layer and forwards an outer abort unchanged.
`handle_outer` then removes the outer layer. The constructor types suffice:
there are no separate request-policy or policy-preservation lemmas.

Both requests carry ownership at state 0. An inner recovery writes 2 and returns
10; an outer recovery must still see state 0 and writes 3. The outer normal
clause changes the intermediate integer result to bool true. There are no
dynamically allocated effect instances or first-class resumptions in this test.

### Native syntax and exact two-exit contracts

For example, `Native.maybe_value` specifies both paths:

```pulse
fn maybe_value (b:bool)
  returns x:int
  ensures pure (not b /\ x == 7)
  raises (fun (e:nat) -> pure (b /\ e == 1))
{
  if (b) { raise 1 } else { 7 }
}
```

A handler gives an explicit contract for exceptions leaving its protected body:

```pulse
try
  returns x:int
  ensures pure (x == (if b then 42 else 7))
  raises (fun (e:nat) -> pure (b /\ e == 1))
{ maybe_value b }
catch { 1 -> { 42 } }
```

The implicit fallback forwards unmatched payloads. Without an outer exception
scope, its reachability must be refuted. `raises (fun _ -> emp)` allows an
exception with no resources; only an impossible assertion such as `pure False`
rules it out. Omitting `raises` does not let a caller discard a possible
exception by ignoring the call's result.

| Definitions | What they establish |
| --- | --- |
| `raise_code`, `catch_code` | A direct throwing call and complete recovery with result 7. |
| `failure`, `failed`, `update_and_raise` | A payload-indexed ownership protocol, state update, and reclamation of an exited local scope. |
| `partial`, `framed_call` | Only `Second` escapes, with its resources and an unrelated framed cell preserved. |
| `reraised`, `translate` | Clauses execute outside their own catch; they can change owned state and re-raise or replace the payload. |
| `handler_inside_scope` | A catch still inside a local's scope can read and update it. |
| `maybe_value`, `catch_then_continue`, `increment_result`, `known_normal` | Precise normal/exceptional branch facts, try as an initializer, native call sequencing, and elimination of an impossible exceptional exit without a handler. |
| `invoke`, `locally_defined`, `countdown` | Higher-order, local, and recursive native functions retain their exceptional contracts. |
| `raw_raise`, `raw_outcome` | Raw semantic outcomes remain explicit data rather than being mistaken for native control effects. |
| `deferred_free`, `cleanup_handles_locally`, `cleanup_local_loop` | Nonraising cleanup frees real heap ownership, and cleanup may use internally contained catches and loop exits. |
| `loop_exit`, `skipped_write`, `raise_read`, `early_return` | Propagation across loops, unreachable continuation code, stateful payload evaluation, and ordinary early return in a native function. |

See the [library guide](../../../../lib/pulse/lib/effects/README.md) for
the derived rules, native result-type convention, and current restrictions.
Native scenarios are not included in `Runtime.test` or its five observations.

### Extensible exceptions

The final group in `Native` uses F*'s shared extensible `exn` rather than raw
numbers or a closed exception datatype:

```fstar
exception BadRequest of nat
exception ConnectionLost of string
```

Both constructors produce `exn`, so every nested contract has type
`exn -> slprop`. Forwarding needs no payload embedding. The exceptional
assertions describe which constructors can occur and what resources they carry;
they do not change the exception value's type.

| Definitions | What they establish |
| --- | --- |
| `is_bad_request` | An explicit match defines the handled domain; exception declarations do not generate closed-datatype `C?` discriminators. |
| `exn_raise` | Raising an arbitrary `exn` transfers ownership at state 1 and reclaims a temporary local. |
| `exn_recover_request` | `BadRequest code` recovers with state and result `code + 1`. Every other exception propagates unchanged, with state 1 and a fact excluding `BadRequest`. |
| `exn_nested` | The inner recovery handles `BadRequest 4`; the outer handler handles `ConnectionLost "database"`. The final state/result is exactly 5 or 42, according to the input flag. |
| `exn_reraised` | Re-raising preserves the string payload while transferring the updated state 2 to the outer handler, which finishes at state 3 with result 42. |
| `RetryLater`, `exn_later_extension` | A constructor declared after the selective handler is forwarded through it without changing its contract. `RetryLater 9` is distinct from `BadRequest 9` despite carrying the same payload type. |

The general selective handler never assumes that it knows all constructors.
Complete recovery in its clients is justified by their precise exceptional
contracts, not by treating `exn` as a closed datatype. The corresponding
rejection scenario below checks that distinction.

## Negative scenarios and their expected failures

| Definition | Invalid claim | Expected error category |
| --- | --- | --- |
| `stale_ownership` | After exchanging 0 for 1, the continuation still owns the cell at 0. | 19: refinement/resource-index proof failure |
| `missing_request_ownership` | Owning a program description suffices to execute it without owning its required cell. | 228: Pulse cannot establish the required ownership |
| `unhandled_exception` | A body whose signature still contains Throw can be treated as an empty-environment computation. | 12: type mismatch |
| `stranded_abort_frame` | An abort can retain another cell outside its request protocol. | 19: resource-index proof failure |
| `abort_as_perform`, `returning_as_abort` | Operation kind can be ignored when choosing a node constructor. | 19: kind refinement failure |
| `downgrade_divergent_step` | A potentially divergent tree can be weakened to terminating. | 19: grade-bound proof failure |
| `ignore_implementation_grade`, `ignore_handler_grade` | A terminating request tree makes its implementation or handler terminate. | 12: grade/computation type mismatch |
| `forget_outer_frame` | Framing an inner tree leaves its outer exception contract unchanged. | 19: signature mismatch |
| `lose_acquired_resource` | Ownership acquired by an embedded action can disappear at an abort. | 19: resource-index proof failure |
| `wrong_exception_state` | The exceptional entry contract at state 1 permits proving a read equals 0. | 19: false pure assertion |

`expect_failure` means the declaration must fail with the indicated category.
It is neither an admitted valid program nor code that the runtime driver calls.
Successful verification of this module is evidence that all twelve misuses were
rejected at the intended boundaries.

`NativeRejected` separately checks:

| Definitions | Rejected behavior | Error |
| --- | --- | --- |
| `ignored_exception`, `cleanup_call_escapes` | Ignoring a native call result to swallow an exception, including across a cleanup boundary. | 19 |
| `captured_exception_exit` | Capturing an enclosing function's exception exit in a local function. | 19 |
| `catch_is_not_termination` | Claiming termination just because a potentially divergent call's exceptions are caught, including under defer. | 228 |
| `cleanup_return_abandons_exception` | Returning out of cleanup and abandoning a pending exception's ownership. | 228 |
| `missing_exception_resource` | Raising without the promised ownership. | 228 |
| `lost_frame`, `reraise_abandons_resource` | Propagating a call or re-raising while abandoning owned resources. | 228 |
| `unmatched`, `unhandled_reraise` | Leaving a possible payload unhandled, or treating a clause as protected by its own catch. | 19 |
| `stale_handler_state` | Recovering with the pre-call state instead of the exceptional state. | 19 |
| `ghost_raise`, `atomic_raise` | Raising in a non-stateful computation. | 228 |
| `escaping_cleanup` | Replacing a pending exit by an exception escaping `defer`. | 19 |
| `escaped_local_permission` | Exporting half a local's permission while also claiming to reclaim it. | 19 |
| `return_abandons_frame` | Using ordinary return inside a try to hide lost ownership behind an impossible normal continuation. | 228 |
| `exn_known_cases_are_not_exhaustive` | Treating the example constructors as exhaustive for an arbitrary value of extensible type `exn`. | 19 |

These are seventeen expected failures, not admitted programs. Both direct
raises and automatically propagated calls must satisfy the ownership checks.

## Build stages and generated files

The installed repository compiler at `stage3/out/bin/fstar.exe` must be available.
From this directory:

```sh
make -j8       # Library + all proofs + extraction + linking + recorded execution
make verify   # Library and example proofs, including expected failures
make extract  # Produce _output/Effects_runtime.ml
make build    # Produce the extracted module and _output/effects.exe
make run      # Build as needed, then explicitly rerun the executable
make clean    # Remove this directory's generated artifacts only
```

`extract`, `build`, and `run` follow the runtime entry's dependencies; default
`make` and `make verify` also check both standalone negative-test modules and
the native scenarios. Use `make verify` for the native proof/checker milestone;
the runtime targets concern only the five-case tree-based entry point.

The library owns its own `_cache`; these examples keep their checked files in
this directory's `_cache`. F* generates `.depend`. Custard produces
`_output/Effects_runtime.ml`, and the Makefile copies `driver.ml` into `_output`
so OCaml's auxiliary files stay there. `_output/effects.out` records successful
execution and makes an unchanged default build a no-op for execution.

The dependency distinctions are intentional:

| Change | Required downstream work |
| --- | --- |
| Library interface | Recheck dependent library/client proofs, then update the runtime if affected. |
| Library implementation only | Recheck that implementation and re-extract/relink/rerun; unchanged client interfaces need no new proof. |
| An example used by Runtime | Recheck its dependents and update the runtime. |
| `Example.Effects.Rejected.fst` only | Recheck the negative scenarios; do not re-extract an unrelated runtime entry. |
| `Example.Effects.Native.fst` or `Example.Effects.NativeRejected.fst` | Recheck affected native proofs; these modules are not runtime-entry dependencies. |
| `driver.ml` only | Relink and rerun; no F* rechecking or extraction is needed. |
| Missing generated runtime artifact | Recreate the missing stage and update its dependents. |

The recursive library build refreshes the parent's view of checked-file
timestamps without touching unchanged files. The Makefile also narrows the
shared rules' blanket `.SECONDARY` behavior so missing runtime artifacts do not
silently remain missing. Cleaning examples does not clean the library cache;
use the library's own `make clean` when that is wanted.

## Editor configuration: `.fst.config.json`

The nearest configuration is used for files in this directory. With the
installed F* VS Code extension, its directory supplies the default working
directory, so paths remain portable within the checkout.

| Field or option | Purpose |
| --- | --- |
| `fstar_exe` | `../../../../../stage3/out/bin/fstar.exe`, the installed compiler used for the development. |
| `include_dirs` | This directory, the effects library source directory, the local example cache, and the library cache. This resolves both source names and current checked interfaces. |
| `--cache_dir _cache` | Reads the example cache; use `make verify` to build dependencies before browsing. |
| `--already_cached ...` | Reuses checked F*/Pulse modules, including the effects library built by its Makefile. Unlike the library's config, it does not exclude `Pulse.Lib.Effects`. |
| `--z3rlimit 10` | Uses the same proof budget as the Makefiles. |
| `--warn_error -321` | Matches the build's unexpected-checked-location warning suppression, not proof-error suppression. |
| `--ext optimize_let_vc` and `--ext fly_deps` | Match the build's verification-condition and dependency-loading settings. |

The JSON files deliberately remain strict JSON; their documentation lives in
these READMEs rather than unsupported JSON comments. After configuration changes
or dependency rebuilds, use **F*: Restart** on already-open files to load a fresh
session. Verification here requires no changes to the proof contracts or admits.
