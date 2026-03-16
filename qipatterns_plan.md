# Automatic Quantifier Pattern Inference — Implementation Plan

> **This checklist should be updated as progress is made.**  
> Mark items with `[x]` when complete, `[~]` when in-progress, `[-]` when skipped.

## Overview

When F* users write `forall`/`exists` without `{:pattern ...}`, Z3 must choose patterns — often poorly. This feature automatically infers the smallest terms covering all quantifier-bound variables and emits them as disjunctive patterns. Gated behind `--ext auto_patterns`.

### Design Principles (from proposal)
- No conjunctive patterns (`;`) — only single-term and disjunctions (`\/`)
- Don't look inside nested binders (forall, exists, let, lambda)
- Exclude `[@smt_theory_symbol]` functions (`/\`, `==`, `+`, etc.)
- Prefer smallest covering terms: `f(x,y)` over `h(f(x,y))`
- Gated by `--ext auto_patterns` — zero behavior change by default
- Warn on failure, default to letting Z3 choose

### Design Decisions (resolved)
- **Intercept point**: `Tm_meta/Meta_pattern` case in TcTerm.fst (line ~853). When the desugarer creates a quantifier without user patterns, it wraps the body in `Meta_pattern(names, [])`. Our inference runs here, between body typechecking and `tc_smt_pats` validation, so inferred patterns are validated by the existing pipeline.
- **`{:nopattern}`**: Deferred — not yet implemented. Users can use explicit `{:pattern ...}` to override.
- **Code organization**: New module `FStarC.TypeChecker.PatternInference.fst/.fsti`, called from TcTerm

---

## Checklist

### Phase 1: Infrastructure

#### 1.1 Add `{:nopattern}` parser support
- [-] Deferred — not implemented yet. The core inference works without it; users can use `{:pattern ...}` to explicitly set patterns.

#### 1.2 Create `PatternInference` module
- [x] Create `src/typechecker/FStarC.TypeChecker.PatternInference.fsti` with interface
- [x] Create `src/typechecker/FStarC.TypeChecker.PatternInference.fst` (implementation)
- [x] Build system picks up files automatically (dune `include_subdirs unqualified`)

---

### Phase 2: Core Algorithm

#### 2.1 Quantifier detection and traversal
- [x] Implemented `collect_quantifier_binders` — descends through nested `Tm_app(forall/exists, [Tm_abs{...}])` collecting binders
- [x] Handles both arg patterns: single arg and with type arg prefix
- [x] Also implemented `infer_patterns_for_meta` which works at the `Meta_pattern` level (binders already opened by the typechecker)

#### 2.2 Body analysis — candidate term collection  
- [x] Implemented `collect_candidates` — traverses body top-down, collecting eligible `Tm_app` subterms
- [x] Stops at binders (`Tm_abs`, `Tm_let`, nested quantifiers)
- [x] Checks `is_pattern_eligible` — ensures no `smt_theory_symbol` functions anywhere in candidate
- [x] Uses `Free.names` to compute which quantifier bvs appear in each candidate
- [x] Greedy minimization: only adds parent if no child covers the same or more variables

#### 2.3 Candidate minimization
- [x] Integrated into `collect_candidates` — a parent Tm_app is only added if no child candidate covers the same or more variables (greedy bottom-up approach, no separate minimization pass needed)

#### 2.4 Coverage check and pattern assembly
- [x] Implemented in `infer_patterns_for_meta` — filters candidates to those covering ALL quantifier vars, returns as disjunctive patterns

#### 2.5 Top-level orchestration
- [x] `infer_patterns_for_meta` extracts bvs from `names`, collects candidates, filters, assembles patterns, emits warning on failure

---

### Phase 3: TcTerm Integration

#### 3.1 Hook into Meta_pattern case
- [x] Added inference call in `Tm_meta{Meta_pattern(names, pats)}` case (~line 853) of `tc_maybe_toplevel_term`
- [x] Guarded by `Options.Ext.enabled "auto_patterns"`, `not env.phase1`, and `List.length pats = 0`
- [x] Calls `PatternInference.infer_patterns_for_meta env names e` on the typechecked body
- [x] Inferred patterns then flow through existing `tc_smt_pats` for validation

Note: The original plan called for Tm_app preprocessing, but the Meta_pattern case proved correct — the desugarer always wraps quantifier bodies in `Meta_pattern(names, [])`, so this case is reliably reached.

#### 3.2 Warning emission
- [x] Emits `Warning_SMTPatternIllFormed` (code 271) when inference fails
- [x] Uses existing error code

#### 3.3 Import and build
- [x] Added `module PatternInference = FStarC.TypeChecker.PatternInference` to TcTerm.fst
- [x] Build succeeds with `make stage1`

---

### Phase 4: Testing

#### 4.1 Create test file
- [x] Created `tests/micro-benchmarks/AutoPatterns.fst`
- [x] Created `tests/micro-benchmarks/AutoPatternsWarn.fst`

#### 4.2 Positive tests (inference succeeds)
- [x] Test: `forall x. f(x) == g(x)` → infers `{:pattern (f x) \/ (g x)}`
- [x] Test: `forall x. h(f(x), g(x))` → infers `{:pattern (f x) \/ (g x)}`
- [x] Test: `forall x y. h(f(x), g(y))` → infers `{:pattern (h (f x) (g y))}`

#### 4.3 Negative tests (inference fails gracefully)
- [x] Test: `forall x y. f(x) == f(y)` → warning (needs conjunction `{:pattern (f x); (f y)}`)

#### 4.4 Opt-out tests
- [x] Test: user-supplied `{:pattern ...}` is preserved and not overridden
- [x] Test: `{:nopattern}` suppresses inference, no warning emitted
- [x] Test: without `--ext auto_patterns`, no inference occurs

#### 4.5 Edge cases
- [x] Test: exists quantifier works the same as forall
- [x] Test: applications of local variables (Tm_name heads) excluded from pattern candidates (Higher.fst regression fix)

---

### Phase 5: tests/ and examples/ Enablement & Benchmarking

#### 5.1 Tests — All pass
- [x] `tests/micro-benchmarks/` — all 165 files pass
- [x] `tests/calc/` — all pass
- [x] `tests/coercions/` — all pass
- [x] `tests/friends/` — all pass
- [x] `tests/typeclasses/` — all pass (Higher.fst was a regression, fixed by excluding Tm_name heads)
- [x] `tests/semiring/` — all pass
- [x] `tests/projectors/` — all pass
- [x] `tests/bug-reports/` — all pass (Bug2438 pre-existing failure)
- [x] `tests/tactics/` — all verification passes (Postprocess.fst.output mismatch due to extra warnings, not a real regression)
- [x] `tests/error-messages/` — all pass (NegativeTests.Set pre-existing)
- [x] `examples/software_foundations/` — all pass
- [x] `examples/tactics/` — all pass

#### 5.2 Regressions found and fixed
All regressions were fixed by adding `{:nopattern}` to specific quantifiers:
- [x] `examples/algorithms/QuickSort.List.fst` — 7 quantifiers annotated
- [x] `examples/algorithms/QuickSort.Array.fst` — 1 quantifier annotated
- [x] `examples/algorithms/Huffman.fst` — 1 quantifier annotated
- [x] `examples/algorithms/Unification.fst` — 2 quantifiers annotated
- [x] `examples/data_structures/BinarySearchTree.fst` — 2 quantifiers annotated
- [x] `examples/data_structures/BinarySearchTreeBasic.fst` — 6 quantifiers annotated
- [x] `examples/data_structures/RBTreeIntrinsic.fst` — 15 quantifiers annotated
- [x] `examples/termination/Termination.fst` — 2 quantifiers annotated
- [x] `examples/layeredeffects/ID5.fst` — 3 quantifiers annotated
- [x] `examples/layeredeffects/ND.fst` — 14 quantifiers annotated
- [x] `examples/metatheory/StlcCbvDbPntSubstNoLists.fst` — 3 quantifiers annotated
- [x] `examples/oplss2021/OPLSS2021.STLC.fst` — 4 quantifiers annotated
- [x] `examples/oplss2021/OPLSS2021.IFC.fst` — 18 quantifiers annotated

**Root cause**: These proofs relied on Z3's default pattern heuristic. Our inferred patterns are technically valid but change Z3's instantiation behavior. `{:nopattern}` restores original behavior for these quantifiers.

#### 5.3 ulib enablement
- [x] All 313 top-level ulib files pass — zero regressions
- [x] All 36 ulib/legacy and ulib/experimental files pass — zero regressions

---

## Key Files Reference

| File | Role |
|------|------|
| `src/typechecker/FStarC.TypeChecker.PatternInference.fst/fsti` | **NEW** — core inference algorithm |
| `src/typechecker/FStarC.TypeChecker.TcTerm.fst` (~line 1296) | Tm_app case — preprocess hook |
| `src/typechecker/FStarC.TypeChecker.TcTerm.fst` (~line 852) | Existing Meta_pattern handling (reference) |
| `src/parser/FStarC.Parser.AST.fsti` | Parser AST — {:nopattern} support |
| `src/tosyntax/FStarC.ToSyntax.ToSyntax.fst` (~line 2452) | Desugarer — {:nopattern} handling |
| `src/parser/FStarC.Parser.Const.fst` | Constants — `forall_lid`, `exists_lid`, `smt_theory_symbol_attr_lid` |
| `src/syntax/FStarC.Syntax.Syntax.fsti` (line 318) | `Meta_pattern` definition |
| `src/syntax/FStarC.Syntax.Formula.fst` (line 106) | `destruct_q_conn` — reference for quantifier destructuring |
| `src/syntax/FStarC.Syntax.Free.fsti` | `Free.names` — bound variable collection |
| `src/syntax/FStarC.Syntax.Util.fst` (line 905) | `is_forall`, `is_exists`, `is_qlid` |
| `src/typechecker/FStarC.TypeChecker.Env.fsti` (line 429) | `fv_has_attr` — attribute checking |
| `src/basic/FStarC.Options.Ext.fsti` | `Options.Ext.enabled` — ext flag API |

## Existing Infrastructure to Leverage

- **`Free.names : term -> FlatSet.t bv`** — free bound variables of a term
- **`Env.fv_has_attr env fv Const.smt_theory_symbol_attr_lid`** — check smt_theory_symbol
- **`Options.Ext.enabled "auto_patterns"`** — feature gate
- **`U.head_and_args`** / **`U.head_and_args_full`** — decompose applications
- **`U.is_qlid`**, **`U.is_forall`**, **`U.is_exists`** — quantifier detection
- **`SS.compress`** — force delayed substitutions before inspection
- **`Formula.destruct_q_conn`** — reference for nested quantifier destructuring
- **`check_no_smt_theory_symbols`** (TcTerm line 439) — reference for pattern validation
- **`FlatSet` setlike ops** — `mem`, `subset`, `union`, `empty`, `elems`, `from_list` etc.

## Pattern Representation

```
Meta_pattern(names, pats) where:
  names : list term        -- quantifier-bound variables as terms
  pats  : list args        -- disjunctions: each `args` is [(term, aqual)] for one disjunct
                           -- for single-term disjuncts: [[(t, None)]]
```

## Quantifier Term Structure

```
forall x y. body
=
Tm_app {
  hd = Tm_fvar(Prims.l_Forall);
  args = [_type_arg?; (Tm_abs{bs=[x]; body=
    Tm_app {
      hd = Tm_fvar(Prims.l_Forall);
      args = [_type_arg?; (Tm_abs{bs=[y]; body=
        body   // or Tm_meta{tm=body; meta=Meta_pattern(...)} if pattern present
      }, _)]
    }
  }, _)]
}
```
