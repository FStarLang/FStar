# Build and test pipeline (make -j4, make -skj4 _test)

## Overview
The top-level Makefile drives a multi-stage bootstrap build. Each stage extracts F* sources with an earlier compiler, then compiles OCaml artifacts with dune, and finally installs staged outputs under `stageN/out`. The stages exist to break the cyclic dependency between the compiler and its own sources, and to validate that later stages produce stable outputs.

## `make -j4` (default goal = `build`, which is target `2`)
`build` is an alias for target `2`, which builds and installs **stage2** (the main compiler `fstar.exe`).

### Stage 0 (seed compiler)
1. **`stage0/out/bin/fstar.exe`**
   - Driven by `stage0/Makefile` target `minimal`.
   - Runs `dune build` and `dune install --prefix=out` to get a seed `fstar.exe`.
   - Installs stage0 ulib sources into `stage0/out/lib/fstar` for later checks.
   - The `.stage0.touch` file tracks changes under `stage0/` to force rebuilds.

### Stage 1 (bootstrap from stage0)
2. **Extract stage1 compiler sources (OCaml) with stage0**
   - `.bare1.src.touch`: `mk/fstar-01.mk` extracts `src/` to `stage1/fstarc.ml/` using `FSTAR_EXE=stage0/out/bin/fstar.exe`.
   - `.tests1.src.touch`: `mk/tests-1.mk` extracts the test harness to `stage1/tests.ml/`.
3. **Build stage1 OCaml artifacts with dune**
   - `stage1/dune` targets build:
     - `fstarc-bare` → `stage1/dune/_build/.../fstarc1_bare.exe`
     - `fstarc-full` → `stage1/dune/_build/.../fstarc1_full.exe`
     - tests binary → `stage1/dune/_build/.../fstarc1_tests.exe`
   - `src/ml` timestamp checks via `.src.ml.touch` ensure dune rebuilds when ML sources change.
4. **Extract stage1 libraries and plugin libraries with stage1**
   - `.alib1.src.touch`: `mk/lib.mk` verifies/extracts ulib into `stage1/ulib.ml/`.
   - `.plib1.src.touch`: `mk/lib.mk` extracts pluginlib into `stage1/ulib.pluginml/`.
   - `stage1/` dune builds `libapp` and `libplugin`.
5. **Install stage1**
   - `.install-stage1.touch`: `make -C stage1 install PREFIX=stage1/out`.
   - Provides `stage1/out/bin/fstar.exe` (installed stage1 compiler) and `stage1/out/lib`.

### Stage 2 (bootstrap from stage1 full compiler)
6. **Extract stage2 compiler sources (OCaml) with stage1 full**
   - `.bare2.src.touch`: `mk/fstar-12.mk` extracts `src/` to `stage2/fstarc.ml/` using `FSTAR_EXE=stage1/dune/.../fstarc1_full.exe`.
   - `.tests2.src.touch`: `mk/tests-2.mk` extracts tests to `stage2/tests.ml/`.
7. **Build stage2 OCaml artifacts with dune**
   - `stage2/dune` targets build:
     - `fstarc-bare` → `stage2/dune/_build/.../fstarc2_bare.exe`
     - `fstarc-full` → `stage2/dune/_build/.../fstarc2_full.exe`
     - tests binary → `stage2/dune/_build/.../fstarc2_tests.exe`
8. **Extract stage2 libraries and plugin libraries**
   - `.alib2.src.touch`: `mk/lib.mk` verifies/extracts ulib into `stage2/ulib.ml/`.
   - `.plib2.src.touch`: `mk/lib.mk` extracts pluginlib into `stage2/ulib.pluginml/`.
   - `stage2/` dune builds `libapp` and `libplugin`.
9. **Install stage2 (final `fstar.exe`)**
   - `.install-stage2.touch`: `make -C stage2 install PREFIX=stage2/out`.
   - This installs the final compiler at `stage2/out/bin/fstar.exe`.

### Why two stages (and a seed)?
- **Stage0** provides a trusted, prebuilt compiler to bootstrap from.
- **Stage1** ensures that sources compile with stage0 and produce a full compiler plus libraries.
- **Stage2** recompiles everything with the stage1 compiler to ensure self-hosting and stability.
- A **stage3 diff** (optional target) checks that stage2 and stage3 extractions match to detect drift.

## `make -skj4 _test`
The `_test` target runs tests against the **stage2** compiler by default.

1. **Ensure stage2 is installed**
   - `_test: stage2` guarantees `stage2/out/bin/fstar.exe` exists.
2. **Set FSTAR_EXE**
   - `_test` sets `FSTAR_EXE ?= $(ABS_PATH stage2/out/bin/fstar.exe)` and passes it down.
3. **Run unit tests, examples, and docs**
   - `_unit-tests`: `make -C tests all FSTAR_EXE=<stage2/out/bin/fstar.exe>`
   - `_examples`: `make -C examples all FSTAR_EXE=<stage2/out/bin/fstar.exe>`
   - `_doc`: `make -C doc/book/code` and `make -C doc/old/tutorial regressions`
4. **How tests execute**
   - Each test/example directory includes `mk/test.mk`, which:
     - Generates `.depend` via `fstar --dep full`.
     - Produces `.checked` files via `fstar -c`.
     - Optionally extracts (`--codegen OCaml`) and builds executables.
     - Runs expected-output comparisons and subdirectory recursion.
   - `-s` makes make quiet, `-k` continues after failures, `-j4` runs in parallel.

## Reproducing the system
To reproduce the build:
1. Provide a stage0 compiler under `stage0/dune` or set `FSTAR_EXTERNAL_STAGE0`.
2. Run `make -j4` to build stage1 and stage2 compilers and install `stage2/out/bin/fstar.exe`.
3. Run `make -skj4 _test` to execute tests/examples/docs using the stage2 compiler.
