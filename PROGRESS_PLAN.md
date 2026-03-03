# Removing `--MLish` from the F* Build System

**Branch:** `fstar2_nomlish` (based on `fstar2`)
**Commit:** `03f22c268d` — "Replace CLI --MLish with per-file #push-options pragmas" (396 files changed, 646 insertions, 64 deletions)
**Goal:** Eliminate the `--MLish` compiler flag from the command-line build pipeline, replacing it with per-file `#push-options "--MLish --MLish_effect FStarC.Effect"` pragmas in each compiler source file.

---

## Background

The F* compiler sources are written in a dialect that uses `--MLish` mode: all function arrows default to an ML-like effect, and interface/implementation interleaving is more lax. Previously, `--MLish` was passed on the command line via hacks in the Makefile (`mk/generic-1.mk` detected `FStarC.` in the filename and injected `--MLish`). This approach was fragile and prevented clean separation of concerns.

The new approach: each compiler `.fst`/`.fsti` file declares its own `#push-options "--MLish --MLish_effect FStarC.Effect"` pragma. The build system no longer needs to inject `--MLish`.

---

## What Has Been Accomplished

### Phase 1: Per-file Pragmas ✅
- [x] Added `#push-options "--MLish --MLish_effect FStarC.Effect"` to all 384 compiler source files (179 `.fst` + 205 `.fsti`, including GenSym.fst)
- [x] Made `"MLish"` and `"MLish_effect"` settable via `#push-options` (`src/basic/FStarC.Options.fst`)
- [x] Stripped UTF-8 BOM from files that had it (Defensive.fst, Ident.fst, etc.)

### Phase 2: Interleaving Fixes ✅
The interleaver (`src/tosyntax/FStarC.ToSyntax.Interleave.fst`) needed significant changes to work with per-file pragmas instead of a global CLI flag:

- [x] Added `iface_has_mlish_pragma` — detects `#push-options "--MLish"` in the `.fsti`
- [x] Added `is_ml_mode` — returns `true` if CLI `--MLish` OR `.fsti` has MLish pragma
- [x] Changed `prefix_one_decl` to accept `ml_mode:bool` parameter
- [x] Extended span pattern from `Tycon` only to `Tycon | Pragma | Exception | TopLevelLet`
- [x] Added `is_val_or_let` helper (matches both `Val` and `TopLevelLet` in interface)
- [x] Added `prefix_filtered` for `TopLevelLet` case — filters matching lets from `iface_prefix_tycons` to avoid E47 duplicates
- [x] Added `Exception` case in `prefix_one_decl` — filters matching exceptions from both `iface_prefix_tycons` AND main `iface` to avoid duplicates
- [x] Updated `interleave_module` and `prefix_with_interface_decls` to pass `ml_mode`

### Phase 3: Supporting Infrastructure ✅
- [x] `src/fstar/FStarC.Universal.fst`: Save/restore `ml_ish` flag in `fly_deps_check` (prevents pragma leaking between files)
- [x] `src/syntax/FStarC.Syntax.DsEnv.fst`: Namespace filter on `check_admits` (only report missing admits for the current module, not transitive deps)
- [x] `src/typechecker/FStarC.TypeChecker.Tc.fst`: Namespace filter on `missing_definition_list` (same rationale)

### Phase 4: Source File Fixes ✅
- [x] `src/interactive/FStarC.Interactive.Ide.fst`: Changed `open FStarC.Interactive.JsonHelper { ... }` to plain `open` (exception projectors not available)
- [x] `src/basic/FStarC.Defensive.fst`: Added `open FStarC.Range` and `open FStarC.Class.PP` (not brought by interleaver because `.fsti` Pragma blocks the Open span)
- [x] Kept duplicate `exception`/`let` declarations in `.fst` files (required for stage0's old interleaver during bootstrap). The new interleaver's `prefix_filtered` deduplicates them.

### Phase 5: Parser Fix ✅
- [x] `src/parser/FStarC.Parser.AST.fst`: Added `PatOp` case to `head_id_of_pat` so operator lets (`let (let!)`, `let (>>=)`, `let (let?)`) are recognized by `definition_lids` — critical for interleaver matching

### Phase 6: Build System ✅
- [x] `mk/generic-1.mk`: Removed `--MLish` hack from both `.checked` and `.extracted` rules
- [x] `mk/generic-0.mk`: Broken from symlink to `generic-1.mk`; now a separate file keeping `--MLish` CLI hack for stage0→stage1 bootstrap
- [x] `mk/fstar-01.mk`, `mk/fstar-12.mk`, `mk/tests-1.mk`, `mk/tests-2.mk`: Added `--warn_error '-361'` (suppresses unpopped push-options warning)
- [x] `src/FStarCompiler.fst.config.json`: Added `-361` to warn_error

### Phase 7: Stage0→Stage1 Build ✅
- [x] Patched `stage0/dune/fstar-guts/fstarc.ml/FStarC_Options.ml` to accept MLish as settable (uncommitted, required because stage0 binary rejects `#push-options "--MLish"` with CFatal Error 65)
- [x] Stage0→stage1 build succeeds (`make .bare1.src.touch`)

### Phase 8: Testing ✅
- [x] All 179 `.fst` compiler files pass `--lax` checking with stage2 binary
- [x] All 204 `.fsti` compiler files pass `--lax` checking with stage2 binary

---

## Commit Summary

**Commit `03f22c268d`** on `fstar2_nomlish` (396 files changed, 646 insertions, 64 deletions):

| Category | Files | Nature of Change |
|----------|-------|-----------------|
| Pragma additions | 384 | `#push-options "--MLish --MLish_effect FStarC.Effect"` after `module` line |
| Interleaving | 1 | `FStarC.ToSyntax.Interleave.fst` — core MLish interleaving via pragma |
| Parser | 1 | `FStarC.Parser.AST.fst` — PatOp case in `head_id_of_pat` |
| Infrastructure | 3 | Options.fst, Universal.fst, DsEnv.fst |
| Source fixes | 3 | Tc.fst, Ide.fst, Defensive.fst |
| Build system | 6 | generic-0.mk, generic-1.mk, fstar-01.mk, fstar-12.mk, tests-1.mk, tests-2.mk |
| Config | 1 | `FStarCompiler.fst.config.json` — `-361` in warn_error |
| OCaml ML fixes | 2 | `FStarC_Extraction_ML_PrintML.ml` — try_with desugaring for both effect modules; `FStarC_Effect.ml` — uncommented try_with fallback |

**Commit 2: `37a3ef43f8`** — "Temporary stage0 patch: make MLish/MLish_effect settable" (1 file)
- `stage0/dune/fstar-guts/fstarc.ml/FStarC_Options.ml` — patched `settable` to accept MLish (temporary, revert after stage0 rebase)

---

## What Remains

### Bootstrap Verification ✅
- [x] **stage0→stage1 build**: `make .bare1.src.touch` succeeds (uses `generic-0.mk` with CLI `--MLish` + per-file pragmas)
- [x] **stage1→stage2 build**: Full stage1 binary built, stage2 extracted+built+installed successfully
- [x] **stage2→stage3 fixpoint**: `diff -r stage2/fstarc.ml stage3/fstarc.ml` — **0 differences** ✅
- [ ] **Run CI tests**: Pushed to remote, CI run [#22535980366](https://github.com/FStarLang/FStar/actions/runs/22535980366) in progress

### Bug Found and Fixed: try_with Desugaring
The `emit` function in `FStarC.Universal.fst` prints all ML modules AFTER all files are processed, at which point `restore_opts()` has reset `--MLish` to CLI value (false). The `try_with_ident()` function in `PrintML.ml` used runtime options to determine the effect module, producing `FStar_All.try_with` at print time while the ML AST contained `FStarC_Effect.try_with`. Fixed by matching both known paths statically.

### Phase 9: Progressive MLish Removal — COMPLETE ✅

All `#push-options "--MLish --MLish_effect FStarC.Effect"` pragmas have been removed from every compiler source file. Zero remain.

**Progress: 389/389 files processed (0 remaining)**

**Key class/library changes made to support removal:**
- `Deq.fsti`: `(=?) : a -> a -> ML bool`
- `Ord.fsti`: `cmp : a -> a -> ML order`, all comparison operators ML
- `Show.fsti`: `show : a -> ML string`
- `Setlike.fsti`: ALL class fields → ML (implementations use ML =?/cmp)
- `HasRange.fsti`: `pos`/`setPos` → ML
- `Monoid.fsti`: `mplus` → ML, `(++)` → ML
- `Monad.fsti`: `return` → ML, `<$>` accepts ML callbacks, `<*>` Tot inner arrows
- `AppEmb.fsti`: `<$>`, `<$$>`, `<*>`, `<**>` accept ML function arguments
- `Common.fsti`: `eq_list`, `max_suffix` accept ML callbacks
- `Binders.fsti`: `boundNames` → ML
- `List.fsti`: ALL higher-order functions (map, fold, filter, etc.) accept ML callbacks
- `Util.fsti`: ALL I/O, higher-order functions → ML
- `Format.fsti`: printer callbacks → ML
- `Order.fsti`: `lex`, `compare_list`, `compare_option` → ML callbacks
- `Primops.Base.fsti`: ALL mk* functions accept ML callbacks, psc_subst → ML
- `Tactics.Monad.fsti`: `mlog` continuation → ML, `bind` already ML
- `Tactics.Interpreter.fsti`: `run_unembedded_tactic_on_ps` tau → ML
- `NBETerm.fsti`: `embedding` class fields → ML, `nbe_cbs` fields → ML
- `Options.fsti`: callback refs → ML (set_option_warning_callback etc.)
- `DsEnv.fsti`: `ugly_sigelt_to_string_hook` → ML, `withenv` → ML
- `Syntax.Util.fsti`: `tts_f`/`ttd_f` → ML, `universe_of_binders` callback → ML

**Short-circuit operator pattern**: `&&` and `||` require pure operands. ML operands must be let-bound first:
```fstar
(* Before *) x =? y && f z
(* After  *) let r1 = x =? y in let r2 = f z in r1 && r2
```

**FStarC.Effect.ML vs FStar.All.ML**: These are different effects (`unit` vs `heap` state). All compiler code must use `FStarC.List.*` (not `FStar.List.*`) when passing ML callbacks.

**Checklist:**
- [x] **Phase 9a**: Remove pragma from 33 fsti-only files + small fst-only files
- [x] **Phase 9b**: Remove pragma from 37 more files via sub-agent
- [x] **Phase 9c**: Fix all cascading downstream failures from class/library changes
- [x] **Phase 9d**: Remove pragma from 27 more fsti files
- [x] **Phase 9e**: Remove pragma from 32 more files
- [x] **Phase 9f**: Remove pragma from 22 fst+fsti pairs (JsonHelper, Const, HashMap, etc.)
- [x] **Phase 9g**: Remove pragma from 9 fst-only files (Hooks, Prettyprint, Primops.Docs, etc.)
- [x] **Phase 9h**: Fix Primops.Base mk* to accept ML callbacks, psc_subst → ML
- [x] **Phase 9i**: Remove pragma from 9 more pairs (Embeddings, Errors, Universal, Builtins, etc.)
- [x] **Phase 9j**: Remove pragma from NBETerm, Normalize, InterpFuns, Krml, ML.Modul, V1/V2.Basic
- [x] **Phase 9k**: Remove pragma from all remaining large files (Syntax.Syntax, Options, Env, Rel, TcTerm, ToSyntax, etc.)
- [x] **Phase 9l**: Fix final cascading failures (tts_f, erase_univs, universe_of_binders, etc.)

### Phase 10: Remove --MLish Compiler Support — TODO
- [ ] **Remove `--MLish` from `config.json`**: After stage0 is updated, config.json no longer needs `--MLish`
- [ ] **Remove `--MLish_effect` from `mk/fstar-01.mk`, `mk/fstar-12.mk`, `mk/tests-1.mk`, `mk/tests-2.mk`**: Dead code
- [ ] **Remove `--MLish` option definition from `FStarC.Options.fst`**: Option registration, getter, settable entry
- [ ] **Remove `ml_ish()` checks from compiler**: ~15 call sites in Rel.fst, TcTerm.fst, etc.
- [ ] **Simplify interleaver**: Remove `ml_mode`, `is_ml_mode`, `iface_has_mlish_pragma`, lax interleaving paths
- [ ] **Full bootstrap rebuild**: stage0→stage1→stage2→stage3 fixpoint verification

### Documentation
- [ ] **Update CONTRIBUTING.md or relevant docs**: Document the migration process and any conventions for effect annotations in compiler sources

---

## Architecture Notes

### Bootstrap Chain
```
stage0 (old binary, locally patched for settable MLish)
  + --MLish from generic-0.mk CLI hack (AND per-file pragmas)
  + --warn_error '-361' from fstar-01.mk
  → stage1 (.checked + .ml extraction) ✅

stage1 (has interleaving fixes + PatOp fix in extracted OCaml)
  + per-file #push-options "--MLish" (NO CLI --MLish)
  + --warn_error '-361' from fstar-12.mk
  → stage2 (.checked + .ml extraction) [pending]

stage2
  + per-file #push-options "--MLish"
  → stage3 (should be identical to stage2) [pending]
```

### Key Design Decisions

1. **`generic-0.mk` is separate from `generic-1.mk`**: Originally a symlink. Had to break it because stage0 needs `--MLish` on CLI (old binary without interleaving fixes), while stage1+ uses per-file pragmas only.

2. **`FStarCompiler.fst.config.json` keeps `--MLish`**: Stage0 doesn't have the interleaving fixes needed to process per-file MLish pragmas correctly. This is a bootstrapping constraint that resolves once stage0 is rebased.

3. **Stage0 binary must be patched**: Error 65 (`OptionNotSettable`) is `CFatal` — cannot be suppressed with `--warn_error`. The stage0 binary's `settable` function must be patched to accept `"MLish"` and `"MLish_effect"`. This is an uncommitted local change.

4. **Duplicate declarations kept in .fst files**: Stage0's old interleaver cannot handle missing declarations (e.g., Monad.fst without `let (let!) = bind` fails). The new interleaver's `prefix_filtered` deduplicates them automatically.

### Interleaving: How Per-File Pragma Works
1. **Detection**: `iface_has_mlish_pragma` scans `.fsti` decls for `PushOptions` containing `"--MLish"`
2. **Mode selection**: `is_ml_mode` returns `Options.ml_ish() || iface_has_mlish_pragma iface`
3. **Lax rules**: In `ml_mode`, interface interleaving allows `TopLevelLet`, `Exception`, `Pragma` in addition to `Tycon` and `Val`
4. **Span/Split/Defer**: Span grabs contiguous `Tycon|Pragma|Exception|TopLevelLet` from iface start. Only `Tycon`/`Pragma` emitted immediately; `Exception`/`TopLevelLet` deferred back to main iface to be matched when their `.fst` counterparts appear.
5. **Duplicate prevention**: `prefix_filtered` removes matching `TopLevelLet`/`Exception` from interface prefix to avoid E47

### Known Subtlety: Stranded Exceptions
When an `.fsti` has an `exception` between `Val` entries (e.g., ML.Term.fsti), the span `(Tycon|Pragma|Exception|TopLevelLet)` can't reach it because it starts with `Val`. The exception stays in the iface and gets appended at module end. The fix: the `.fst` keeps its own `exception` declaration, and the `Exception` case in `prefix_one_decl` filters the matching exception from the main `iface` to prevent duplicates.

### PatOp Fix
`head_id_of_pat` in `FStarC.Parser.AST.fst` was missing the `PatOp` case. Operator lets (`let (let!) = bind`, `let (>>=) = bind`, `let (let?) o f = ...`) parsed as `PatOp` patterns, causing `lids_of_let`/`definition_lids` to return `[]`. This meant `maybe_get_iface_vals` could never match these declarations, leaving `.fsti` copies stranded → E47 duplicates.
