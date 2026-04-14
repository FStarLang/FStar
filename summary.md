# fix/windows-misc Branch Summary: Dune-Based Build System for F*

## Goal
Replace GNU Make + POSIX shell build with a pure dune build portable across
Linux, macOS, and Windows (PowerShell / MSYS2).

## What Was Done

### 1. `--dep dune` Feature (F* source changes)

Added `fstar.exe --dep dune` which outputs `(rule ...)` stanzas for dune.
Key F* source modifications:

- **`FStarC.Options`**: Added `MLish` (bool) and `MLish_effect` (string) options
  controlling per-module ML-ish extraction behavior.
- **`FStarC.Dependencies` / `FStarC.Parser.Dep`**: Added `print_dune` function
  that generates dune `(rule ...)` stanzas. Each rule:
  - Uses `%{env:FSTAR_EXE=fstar.exe}` (not `%{fstar}` — dune has no built-in fstar var)
  - Outputs `.checked.lax` targets for verification rules
  - Outputs `.ml`/`.krml` targets for extraction rules  
  - Respects `--extract` flags for suppressing extraction of specific modules
  - Only applies `--MLish` flags to `FStarC.*` modules, NOT to `FStar.*`/`Prims.*`
- **`FStarC.Filepath`**: Added `make_relative_to` function computing relative
  paths between absolute paths. Handles:
  - Windows/Unix path separators
  - Case-insensitive comparison on Windows
  - `../../` sequences for escaping dune `_build` directory
  - Paths normalized by dune (which absolutizes include paths via `_build/`)
- **krml extraction**: Fixed to respect `--extract` flags (was unconditional)

### 2. Two-Phase Extraction Pattern

The key pattern (proven in `examples/hello/`):
```dune
; Generator rules (in sibling *-gen/ dir to avoid dynamic_include cycles)
(rule
  (target deps.build.inc)
  (deps (universe))
  (action (with-stdout-to %{target}
    (run %{env:FSTAR_EXE=fstar.exe} --dep dune --output_ext fst.checked
         --already_cached "Prims FStar" %{workspace_root}/../../Hello/))))

(rule
  (target deps.extract.inc)
  (deps (universe))
  (action (with-stdout-to %{target}
    (run %{env:FSTAR_EXE=fstar.exe} --dep dune --output_ext ml --codegen OCaml
         --already_cached "Prims FStar" %{workspace_root}/../../Hello/))))

; Consumer rules (in project dir)
(dynamic_include ../Hello-gen/deps.build.inc)
(dynamic_include ../Hello-gen/deps.extract.inc)
(executable (name Hello) (libraries fstar.lib))
```

**Important**: Generator and consumer MUST be in sibling directories
(not parent→child) to avoid `dynamic_include` cycles in dune.

### 3. Dune Infrastructure (repo root)

Created at repo root:
- `dune-project`: `(lang dune 3.15)`, `(using menhir 2.1)`, package `fstar`
  with all OCaml deps (batteries, zarith, stdint, menhir, sedlex, ppxlib, etc.)
- `dune`: root-level dune file
- `dune-workspace`: workspace config

### 4. Stage0 Flattening

Flattened `stage0/dune/` into `stage0/` directly:
- Moved `fstar-guts/`, `fstar-plugins/`, `fstarc-bare/`, `fstarc-full/`
  up one level from `stage0/dune/` to `stage0/`
- Created `stage0/dune-project` (separate dune root, `(lang dune 3.8)`)
- Removed `stage0/Makefile`, `stage0/mk/`, `stage0/README.md`, etc.
- Added `stage0/.scripts/dune` with `(dirs :standard .scripts)` to include
  dot-directories that dune ignores by default
- Stage0 builds with: `dune build --root=stage0 @install`
  (**Must use `@install`**, not just `dune build`, to generate `.install` files
  needed by `dune install`)

### 5. Extraction via `fstarc.dune.inc`

Created `src/extracted/dune` with:
- `copy_files` directives for all source directories (ulib, src/basic, src/class,
  ..., src/tests, including `ulib/legacy/`)
- Rule to generate `fstarc.dune.inc` using:
  ```
  fstar.exe --lax --MLish --MLish_effect FStarC.Effect --dep dune
            --include ../../ulib --include ../basic ... --include ../tests
            --extract FStarC --extract +FStar.Pervasives
            --extract -FStar.Pervasives.Native --extract "krml:-*"
  ```
- The `(include fstarc.dune.inc)` must be COMMENTED OUT during generation phase
  and UNCOMMENTED for extraction phase (chicken-and-egg with dune file parsing)
- `extract-stage1` alias depends on `fstarc.dune.inc` (generation phase) or
  `FStarC_Main.ml` (extraction phase)

### 6. Unified Makefile

Replaced 900+ line Makefile + `mk/*.mk` with ~140 lines:
```makefile
# Platform-portable commands
ifeq ($(OS),Windows_NT)
  RM = powershell -Command "Remove-Item -Recurse -Force ..."
  MKDIR = powershell -Command "New-Item -ItemType Directory -Force"
else
  RM = rm -rf
  MKDIR = mkdir -p
endif

# Sequential build chain
build: stage2
extract: stage0        # stage0 must finish before extract
stage1: extract        # extract must finish before stage1
stage2: stage1         # stage1 must finish before stage2

stage0: dune build --root=stage0 @install
extract: dune build @extract-stage1
stage1: dune build @stage1
stage2: dune build @stage2
```

**Critical**: Without explicit dependency declarations, `make -j` runs
stages in parallel causing dune lock file conflicts (`_build/.lock`
expects integer PID, finds empty).

### 7. Packaging Rules (`packaging/dune`)

Pure dune rules for `package`, `package-src`, `install-fstar` aliases.
**Still uses bash scripts** in `(run bash -c "...")` — NOT yet portable.
Uses `rsync`, `tar`, `uname` — POSIX-only.

### 8. Windows CI (MSYS2)

- `ocaml/setup-ocaml@v3` has hardcoded Cygwin mirror `mirrors.kernel.org`
  that fails from GitHub Actions IPs (error 12002, signature failures)
- Issue: https://github.com/ocaml/setup-ocaml/issues/1038
- Fix: Use `msys2/setup-msys2@v2` (UCRT64) + `tobil4sk/setup-ocaml@feature/msys2`
  fork with `windows-environment: msys2`
- Default shell: `msys2 {0}` (replaces `bash` which assumed Cygwin)
- Install packages: base-devel, mingw-w64-ucrt-x86_64-gcc/gmp/libffi, m4, make, etc.
- `ldd` regex for libgmp fixed: `[[:space:]]` → `[[:space:]]*`

### 9. Nix Build Updates

- `flake.nix`: Changed to `ocamlPackages_5_4`, uses `buildDunePackage` with
  custom make phases
- `.nix/fstar.nix`: Simplified deps (removed `util-linux`, `which`, `num`,
  `karamel-src`, `karamelOcamlDeps`), uses make phases:
  ```nix
  buildPhase = "make -j$NIX_BUILD_CORES";
  installPhase = "make install PREFIX=$out";
  ```

### 10. Docker/Devcontainer

- Updated base images to use `dune` instead of `make -C stage0`
- `.docker/build/build_funs.sh`: Changed build commands to use dune
- `.devcontainer/minimal.Dockerfile`: Updated for dune workflow

## Lessons Learned / Issues

1. **`dynamic_include` cycles**: Generator and consumer dirs must be siblings,
   not parent→child. The `examples/hello` pattern uses `Hello-gen/` alongside `Hello/`.

2. **`%{env:FSTAR_EXE=fstar.exe}`**: Dune has no `%{fstar}` variable. Must use
   env var. The `--ocamlenv` feature sets this up: `fstar.exe --ocamlenv dune build`.

3. **Stage0 as separate dune root**: Stage0 MUST be a separate `--root=stage0`
   because it defines package `fstar` which conflicts with the root project's
   package of the same name.

4. **Windows path case sensitivity**: `Prims.fst` vs `prims.fst` caused issues.
   `make_relative_to` uses case-insensitive comparison on Windows.

5. **Dune absolutizing paths**: When dune copies sources to `_build/`, include
   paths get absolutized. The `make_relative_to` function must handle paths
   like `C:/.../build/default/src/extracted/../../ulib/...`.

6. **krml extraction was unconditional**: Had to fix F* to respect `--extract`
   flags for krml output, not just OCaml.

7. **Packaging still uses bash**: The `packaging/dune` rules still run bash
   scripts with POSIX commands. NOT portable to Windows PowerShell.

8. **FSTAR_LINK_LIBDIRS / symlinks**: Master uses `ln -Tsrf` for local installs
   to get VS Code integration. Must replace with copies or dune mechanisms.

## What Remains for Full Portability

The `examples/hello` pattern on master (using `--dep dune` + `--output_ext` +
`dynamic_include`) is the blueprint. To make the full build portable:
1. **Bump stage0** so fstar0.exe has `--dep dune` and `--output_ext`
   (the current stage0 snapshot predates these features)
2. Apply the `dynamic_include` pattern to stages 1-3 extraction
3. Replace `packaging/dune` bash scripts with portable dune rules
4. Eliminate all `ln -Tsf`, `find -exec`, `flock`, `env`, `sed -i`, `rsync`
5. Use `--ocamlenv` for automatic OCAMLPATH setup

## Stage0 Bump Requirement

**CRITICAL**: The current stage0 snapshot does NOT have `--dep dune` or
`--output_ext`. These features are in master's F* source code but the
stage0 OCaml snapshot predates their addition.

**Recommended approach**: Bump stage0 on Linux. The Windows build system
has several issues that make bumping on Windows impractical:
1. Cygwin path encoding: Native Windows binaries (built by dune/mingw)
   get garbled paths when env vars pass through Cygwin `env` command
2. Symlinks: stage1/dune/ uses symlinks extensively, which break on Windows.
   Must be replaced with file copies.
3. `FSTAR_LIB`: The Makefile uses Cygwin-style absolute paths that native
   Windows binaries can't parse. Fixed with `$(call cygpath,...)` wrapper.
4. `--already_cached` + missing checked files: stage2 extraction expects
   Prims to be pre-cached but the checked files aren't in the right location.

```bash
# On Linux, from master:
make bump-stage0 ADMIT=1
git add stage0/ && git commit -m "Bump stage0 with --dep dune support"
```

## Dune Build Infrastructure (build/ directory)

The `build/` directory contains a standalone dune project that builds F*
through its staged bootstrap using `--dep dune`:

```
build/
├── dune-project    # (lang dune 3.15)
├── dune            # Generator rules in (subdir stage1-gen ...)
├── stage1-gen/     # Generated .inc files (fstarc.build.inc, fstarc.extract.inc)
└── stage1/         # Consumer: (dynamic_include), builds fstar1.exe
    └── dune
```

Usage (after stage0 bump):
```bash
# 1. Build stage0
dune build --root=stage0/dune @install
dune install --root=stage0/dune --prefix=stage0/out

# 2. Build stage1 using fstar0.exe
FSTAR_EXE=stage0/out/bin/fstar.exe dune build --root=build @stage1
```
