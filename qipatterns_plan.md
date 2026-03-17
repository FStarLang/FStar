# Automatic Quantifier Pattern Inference — Implementation Plan

> **This checklist is updated as progress is made.**

## Overview

When F* users write `forall`/`exists` without `{:pattern ...}`, Z3 must choose patterns — often poorly. This feature automatically infers the smallest terms covering all quantifier-bound variables and emits them as disjunctive patterns. Gated behind `--ext auto_patterns`.

## Status Summary

### Completed
- [x] Core algorithm in `FStarC.TypeChecker.PatternInference.fst/.fsti`
- [x] TcTerm integration at `Tm_meta/Meta_pattern` case
- [x] `{:nopattern}` parser syntax (lexer, parser, AST, desugarer)
- [x] `{:nopattern}` semantics: produces `Meta_pattern([], [])` to preserve baseline SMT encoding while suppressing inference
- [x] `is_head_fvar` check: exclude local variable applications from patterns
- [x] Diagnostic messages with failure reasons (3 categories)
- [x] `--ext auto_patterns_diag` for success reporting
- [x] ulib annotated: ~290 `{:nopattern (* uninferrable *)}` across 64 files
- [x] ulib builds clean in BOTH baseline and auto_patterns modes (349/349)
- [x] examples/ annotated with `{:nopattern (* override *)}` where needed (13 files)
- [x] tests/ annotated where needed

### Remaining Work
- [ ] Full clean two-branch benchmark (baseline fstar2 vs fstar2_autopatterns with --ext auto_patterns everywhere)
- [ ] Fix remaining test/example regressions when ulib has auto_patterns baked into .checked files
- [ ] Pulse: update parser, annotate, benchmark
- [ ] Update benchmark scripts in tools/

## Architecture

### Key files
| File | Role |
|------|------|
| `src/typechecker/FStarC.TypeChecker.PatternInference.fst/i` | Core inference algorithm |
| `src/typechecker/FStarC.TypeChecker.TcTerm.fst` (~line 862) | Integration point |
| `src/ml/FStarC_Parser_LexFStar.ml` | `{:nopattern` lexer token |
| `src/ml/FStarC_Parser_Parse.mly` | Parser rule for `{:nopattern}` |
| `src/parser/FStarC.Parser.AST.fsti` | `patterns` type with nopattern flag |
| `src/tosyntax/FStarC.ToSyntax.ToSyntax.fst` | Desugarer: `Meta_pattern([], [])` for nopattern |

### {:nopattern} semantics
- `{:nopattern}` → desugarer produces `Meta_pattern([], [])` (empty names, empty pats)
- This PRESERVES the `Meta_pattern` wrapper (baseline SMT encoding unchanged)
- TcTerm skips inference when `names` is empty
- Convention: `{:nopattern (* uninferrable *)}` = inference fails, `{:nopattern (* override *)}` = inference succeeds but produces a bad pattern

### Annotation conventions
- `{:nopattern (* uninferrable *)}` — no eligible pattern candidates found
- `{:nopattern (* override *)}` — inference produces a valid pattern but it breaks the proof (with explanation in comment)
- `{:pattern ...}` — user-supplied explicit pattern (always respected)

## Benchmarking approach
Two clean builds in separate directories:
1. **Baseline**: `fstar2` branch, vanilla build (no `--ext auto_patterns`)
2. **Head**: `fstar2_autopatterns` branch, `--ext auto_patterns` everywhere (ulib + tests + examples)

Compare: wall time, Z3 rlimit, query counts, memory (peak RSS)
