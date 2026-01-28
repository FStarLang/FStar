# Session Summary: F* Dune Migration

**Date:** 2026-01-25

## Build Status
- **Stage 0:** ✅ Working - `dune build @stage0` completes successfully
- **Extraction:** ✅ Working - `dune build @extract-stage1` extracts 177 .ml files
- **Stage 1:** ✅ Working - `dune build @stage1` compiles 217 object files to library
- **Stage 2:** ❌ Not implemented yet

## How to Build
```bash
npm install -g esy
esy install

# Step 1: Build stage0 (bootstrap compiler from snapshot)
dune build @stage0     # ~10 min

# Step 2: Extract F* sources to OCaml
dune build @extract-stage1  # ~30 min (promotes 177 .ml files to src/extracted/)

# Step 3: Build stage1 library from extracted + hand-written files  
dune build @stage1     # ~5 min (compiles 217 .cmx files)
```

The stage0 F* compiler is built at: `_build/default/stage0/dune/fstarc-full/fstarc2_full.exe`
The stage1 library is built at: `_build/default/src/stage1/fstarcompiler_stage1.cmxa`

## Key Changes Made

### 1. Pure Dune Architecture
- Single dune context (no stage0/1/2 contexts)
- Use aliases: `@stage0`, `@extract-stage1`, `@stage1`
- Use `(promote (until-clean))` to promote extracted files

### 2. Python Extraction Script (.scripts/extract.py)
- Portable across Windows, Linux, macOS
- Handles `--MLish` flag correctly per-module:
  - FStar.* modules: NO `--MLish`
  - FStarC.* modules: WITH `--MLish --MLish_effect FStarC.Effect`
- Verifies all ulib files first to populate cache
- Then extracts FStarC modules using the cache

### 3. Stage1 Library (src/stage1/dune)
- Uses copy_files to combine:
  - src/extracted/*.ml (177 extracted files)
  - src/ml/*.ml (36 hand-written files)  
  - src/ml/*.mly (2 parser grammar files)
- Depends on fstar_ulib library for runtime support
- Compiles to fstarcompiler_stage1.cmxa (217 modules)

### 4. Files Modified/Created
- `dune-workspace` - Single default context
- `stage0/dune/fstarc-full/dune` - Added @stage0 alias
- `src/extracted/dune` - Extraction rule with promote
- `.scripts/extract.py` - Portable extraction script
- `src/stage1/dune` - Stage1 library definition
- `ulib/ml/dune` - PPX and directory config
- `ulib/ml/plugin/dune` - Empty (disable plugin files)
- `ulib/ml/app-extra/dune` - Empty (disable app-extra files)
- `session.md` - This file

### 5. Disabled Files (renamed to .ml.disabled)
- ulib/ml/plugin/*.ml - Depend on fstarcompiler (circular)
- ulib/ml/app-extra/*.ml - Depend on extracted modules

## Next Steps
1. Create stage1 executable (fstar_stage1.exe)
2. Use stage1 to extract stage2 files
3. Build stage2 executable
4. Finalize build, remove bash scripts

## Architecture Notes

### Extraction Complexity
The `--MLish` flag can only be applied globally to an F* invocation, but:
- FStarC.* modules NEED `--MLish` (they use FStarC.Effect.ALL)
- FStar.* and Prims.* modules FAIL with `--MLish`

The Python script solves this by:
1. First verifying ALL ulib files (no --MLish) to populate cache
2. Then verifying/extracting FStarC modules with --MLish, using cached ulib
