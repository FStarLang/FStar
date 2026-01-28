# F* Pure Dune Migration Plan

## Goal
Migrate the F* compiler build from Makefile+bash scripts to pure Dune, using `(promote)` for multi-stage bootstrap. Use `--lax` mode for stages 0→2, full verification only at the final stage.

## Current State
- **Stage 0**: ✅ Works - builds from OCaml snapshot in `stage0/dune/fstar-guts/`
- **Stage 1/2**: ❌ Disabled - extraction rules need implementation
- **Shell script**: `.scripts/build_stages.sh` - want to eliminate

## Key Insight from Legacy Makefile

The legacy build has three types of OCaml files:

1. **Hand-written ML files** (`src/ml/*.ml`) - ~40 files like `FStarC_Util.ml`, `FStarC_List.ml`
   - These are fundamental OCaml implementations, NOT extracted from F*
   - Copied to each stage's build directory
   - Trigger rebuilds when modified (tracked via `.src.ml.touch`)

2. **Extracted ML files** (`stageN/fstarc.ml/*.ml`) - ~177 files
   - Generated from F* sources via `--codegen OCaml`
   - Different for each stage (stage1 extracts with stage0, stage2 with stage1)

3. **App/Plugin ML files** (`ulib/ml/app/*.ml`, `stageN/plugins.ml/`)
   - Runtime library and plugin implementations

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────────┐
│                        DUNE BUILD FLOW                               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  stage0/dune/fstar-guts/                                            │
│    ├── fstarc.ml/*.ml     (177 committed snapshot extracted files)  │
│    ├── ml/*.ml            (40 hand-written, copy of src/ml/)        │
│    └── app/*.ml           (runtime library)                         │
│           │                                                          │
│           ▼                                                          │
│  ┌─────────────────┐                                                │
│  │ Stage 0 Build   │  fstarcompiler lib → fstarc2_full.exe          │
│  └────────┬────────┘                                                │
│           │                                                          │
│           ▼ (extraction using stage0 binary)                        │
│  ┌─────────────────┐                                                │
│  │ Stage 1 Extract │  fstar.exe --lax → src/extracted/*.ml          │
│  └────────┬────────┘  (promoted to source tree)                     │
│           │                                                          │
│           │ + src/ml/*.ml (hand-written, always used)               │
│           ▼                                                          │
│  ┌─────────────────┐                                                │
│  │ Stage 1 Build   │  Compile → fstar_stage1.exe                    │
│  └────────┬────────┘                                                │
│           │                                                          │
│           ▼ (extraction using stage1 binary)                        │
│  ┌─────────────────┐                                                │
│  │ Stage 2 Extract │  fstar_stage1 --lax → src/extracted/*.ml       │
│  └────────┬────────┘  (promoted, overwrites stage1 files)           │
│           │                                                          │
│           │ + src/ml/*.ml (hand-written, always used)               │
│           ▼                                                          │
│  ┌─────────────────┐                                                │
│  │ Stage 2 Build   │  Compile → fstar_stage2.exe (FINAL)            │
│  └─────────────────┘                                                │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

## Key Design Decisions

### 1. Directory Structure
```
src/
├── ml/                  # Hand-written OCaml (fundamental, not extracted)
│   ├── FStarC_Util.ml
│   ├── FStarC_List.ml
│   └── ... (~40 files)
├── extracted/           # Extracted from F* (promoted by dune)
│   ├── FStarC_Common.ml
│   ├── FStarC_Syntax_Syntax.ml
│   └── ... (~177 files)
├── basic/               # F* sources
├── syntax/              # F* sources
└── ...
```

### 2. Promote Strategy
- Use `(mode (promote (until-clean)))` for extracted .ml files
- Files promoted to `src/extracted/` directory
- Hand-written `src/ml/` files are NOT promoted - they're source
- `dune clean` removes promoted files

### 3. Extraction Flags
```
--lax                      # Lax typechecking (fast)
--MLish                    # For FStarC.* modules only
--MLish_effect FStarC.Effect
--codegen OCaml
--already_cached '*,'      # Use cached deps, don't re-verify
--admit_smt_queries true   # Skip SMT (belt and suspenders)
--extract 'FStarC'         # Extract compiler modules
--extract '+FStar.Pervasives'
--extract '-FStar.Pervasives.Native'
```

### 4. Single Context with Aliases
- One default context
- Use aliases: `@stage0`, `@extract-stage1`, `@stage1`, `@extract-stage2`, `@stage2`
- Promote files between extraction and build phases

---

## Implementation Plan

### Phase 1: Infrastructure Setup
- [ ] **1.1** Create `src/extracted/` directory
- [ ] **1.2** Create `src/extracted/dune` with extraction rule + library
- [ ] **1.3** Update `dune-workspace` to single default context
- [ ] **1.4** Add `src/ml/dune` for hand-written files library
- [ ] **1.5** Ensure stage0 still builds with new structure

### Phase 2: Stage 0 → Stage 1 Extraction
- [ ] **2.1** Add extraction rule in `src/extracted/dune`
  - Uses `%{exe:stage0/dune/fstarc-full/fstarc2_full.exe}`
  - Targets: all ~177 extracted .ml files
  - Mode: `(promote (until-clean))`
- [ ] **2.2** Generate target file list from stage0 snapshot
- [ ] **2.3** Test: `dune build @extract-stage1`
- [ ] **2.4** Verify promoted files appear in `src/extracted/`

### Phase 3: Stage 1 Build
- [ ] **3.1** Create library combining:
  - `src/extracted/*.ml` (extracted)
  - `src/ml/*.ml` (hand-written)
- [ ] **3.2** Add menhir rules for parsers
- [ ] **3.3** Add FStarC_Version.ml generation
- [ ] **3.4** Create stage1 executable
- [ ] **3.5** Test: `dune build @stage1`

### Phase 4: Stage 1 → Stage 2 Extraction
- [ ] **4.1** Add extraction rule using stage1 binary
- [ ] **4.2** Promote to same `src/extracted/` (overwrites stage1 files)
- [ ] **4.3** Test: `dune build @extract-stage2`

### Phase 5: Stage 2 Build
- [ ] **5.1** Build stage2 executable from fresh extracted files
- [ ] **5.2** Test: `dune build @stage2`
- [ ] **5.3** Verify stage2 binary works: `./fstar_stage2.exe --version`

### Phase 6: Finalization
- [ ] **6.1** Add `@all` alias that builds stage2
- [ ] **6.2** Update `package.json` build command
- [ ] **6.3** Remove `.scripts/build_stages.sh`
- [ ] **6.4** Update session.md and documentation
- [ ] **6.5** Test full build: `esy build`

### Phase 7: Full Verification (Optional)
- [ ] **7.1** Add `@verify` alias for full verification
- [ ] **7.2** Cache .checked files for reuse

---

## Detailed File Changes

### `dune-workspace`
```lisp
(lang dune 3.0)
; Single context - stages managed via aliases and promote
(context default)
```

### `src/ml/dune` (hand-written files)
```lisp
; Hand-written OCaml files - fundamental compiler implementation
; These are NOT extracted from F*, they are source files

(library
 (name fstar_handwritten)
 (modules :standard)
 (libraries batteries zarith stdint yojson pprint sedlex menhirLib)
 (preprocess (pps ppx_deriving.show ppx_deriving_yojson sedlex.ppx)))
```

### `src/extracted/dune`
```lisp
(include_subdirs unqualified)

; Extraction rule: Stage0 → Stage1
(rule
 (alias extract-stage1)
 (targets FStarC_Common.ml FStarC_Const.ml ... ) ; ~177 files
 (mode (promote (until-clean)))
 (deps
   (file %{project_root}/stage0/dune/fstarc-full/fstarc2_full.exe)
   (source_tree %{project_root}/src/basic)
   (source_tree %{project_root}/src/syntax)
   ; ... other source trees
   (source_tree %{project_root}/ulib))
 (action
   (run %{project_root}/stage0/dune/fstarc-full/fstarc2_full.exe
     --lax
     --MLish_effect FStarC.Effect
     --codegen OCaml
     --odir .
     --cache_dir %{project_root}/_build/default/cache/stage1
     --admit_smt_queries true
     --already_cached '*,'
     --extract FStarC
     --extract +FStar.Pervasives
     --extract -FStar.Pervasives.Native
     --include %{project_root}/src/basic
     ; ... other includes
     %{project_root}/src/fstar/FStarC.Main.fst)))

; Library from extracted files
(library
 (name fstar_extracted)
 (libraries fstar_handwritten)
 (preprocess (pps ppx_deriving.show ppx_deriving_yojson sedlex.ppx))
 (flags -w -8-20-26-27-28-33-35))

; Stage 1 extraction uses stage0 binary
; Stage 2 extraction uses stage1 binary (separate rule with different deps)
```

### `src/dune` (executables)
```lisp
; Stage 1 executable
(executable
 (name fstar_stage1)
 (libraries fstar_extracted fstar_plugins fstar_ulib memtrace)
 (link_flags -linkall))

; Stage 2 uses same structure but different extraction
```

---

## Risk Mitigation

| Risk | Mitigation |
|------|------------|
| Extraction takes too long | `--lax` + `--admit_smt_queries`, parallelize with dune |
| Circular dependency | Extracted files in separate dir, hand-written always available |
| Module name conflicts | `src/ml/` and `src/extracted/` are distinct |
| Stage2 overwrites stage1 | Intentional - only keep latest extraction |

---

## Success Criteria
1. `dune build @stage0` - builds bootstrap compiler ✅ (already works)
2. `dune build @extract-stage1` - extracts using stage0
3. `dune build @stage1` - compiles stage1 from extracted + hand-written
4. `dune build @extract-stage2` - extracts using stage1
5. `dune build @stage2` - compiles final compiler
6. `dune build` or `esy build` - full build works
7. No shell scripts required
8. Works on Windows, Linux, macOS

---

## Timeline Estimate
- Phase 1: 1 hour (infrastructure)
- Phase 2: 2-3 hours (extraction rule, file list generation)
- Phase 3: 2 hours (stage1 build)
- Phase 4-5: 2 hours (stage2)
- Phase 6-7: 1-2 hours (cleanup)
- **Total: ~8-10 hours**
