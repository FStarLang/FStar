# Effects examples: what is verified and what is executed

This directory exercises the resource-indexed effects library in
[`lib/pulse/lib/effects`](../../../../lib/pulse/lib/effects/README.md).
The progression is ordinary operations, one abortive exception layer, then
nested layers whose forwarding preserves the enclosing handler's ownership
discipline. Negative examples check that plausible but invalid uses are rejected.

Read the modules in the order below. Each definition has an adjacent explanation
of its role, the ownership it consumes/returns, or the scenario it exercises.

## File map

| File | What to look for |
| --- | --- |
| [`Example.Effects.Core.fst`](Example.Effects.Core.fst) | Delayed heap actions, an operation with a state-changing request/reply contract, explicit tree framing, an erased old-state witness, consequence, and forwarding through an exception layer that cannot throw. |
| [`Example.Effects.Exception.fst`](Example.Effects.Exception.fst) | A throwing branch and a normal branch, exact recovery ownership, unreachable continuation code, and framing around the handled result. Its local function `handle` uses library `X.catch`, not `X.handle`. |
| [`Example.Effects.Nested.fst`](Example.Effects.Nested.fst) | Two unit-payload exception layers distinguished by tags. Explicit policy proofs make an inner catch produce a computation admissible to an outer catch. The handlers change the result type from empty to int to bool. |
| [`Example.Effects.Rejected.fst`](Example.Effects.Rejected.fst) | Five expected verification failures: stale ownership, missing ownership, an unresolved effect, a stranded private frame, and a wrong exception-entry state. Not an executable test module. |
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

### Nested routing and policy preservation

The two layers both use unit payloads. An inner request uses `Throw`; an outer
request, seen from the inner environment, uses `Other Throw`. This tests static
layer identity independently of payload type.

`request_inner` and `request_outer` each establish the inner frame policy and
the forwarded outer policy. `prefix` carries both through a preparatory Pulse
step. `handle_inner` uses `catch_all_requests` to retain the outer policy after
removing the inner layer. Without that fact, an unrestricted result tree would
not suffice for the outer `catch`.

Both requests carry ownership at state 0. An inner recovery writes 2 and returns
10; an outer recovery must still see state 0 and writes 3. The outer normal
clause changes the intermediate integer result to bool true. There are no
dynamically allocated effect instances or first-class resumptions in this test.

## Negative scenarios and their expected failures

| Definition | Invalid claim | Expected error category |
| --- | --- | --- |
| `stale_ownership` | After exchanging 0 for 1, the continuation still owns the cell at 0. | 19: refinement/resource-index proof failure |
| `missing_request_ownership` | Owning a program description suffices to execute it without owning its required cell. | 228: Pulse cannot establish the required ownership |
| `unhandled_exception` | A body whose signature still contains Throw can be treated as an empty-environment computation. | 12: type mismatch |
| `stranded_frame` | A Throw retaining another cell outside its exceptional protocol satisfies the safe-catch refinement. | 19: frame-policy proof failure |
| `wrong_exception_state` | The exceptional entry contract at state 1 permits proving a read equals 0. | 19: false pure assertion |

`expect_failure` means the declaration must fail with the indicated category.
It is neither an admitted valid program nor code that the runtime driver calls.
Successful verification of this module is evidence that all five misuses were
rejected at the intended boundaries.

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
`make` and `make verify` also check the standalone negative-test module.

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
