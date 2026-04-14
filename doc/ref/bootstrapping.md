# Bootstrapping

The F\* compiler is written in F\*, extracted to OCaml, and compiled
with dune.  The build uses a multi-stage bootstrapping process to
ensure that the compiler can compile itself.

## Components

The compiler has three main components:

- **Compiler** (`src/`): The F\* compiler source code (FStarC.\*
  modules), extracted to OCaml.
- **Plugins** (`ulib/`): Tactic and metaprogramming plugins
  (FStar.Tactics.\*, etc.), extracted from the standard library using
  `--codegen PluginNoLib`.
- **Standard library** (`ulib/`): The F\* standard library (Prims,
  FStar.\* modules), verified and extracted to OCaml.

## Stages

### Stage 0

A pre-built OCaml snapshot of the compiler, stored in `stage0/`.  It
contains extracted OCaml sources and a dune build configuration, but
no copy of the standard library.  Stage 0 is periodically updated via
`make bump-stage0`.

### Stage 1

Built by the stage 0 compiler using the current ulib:

1. **Extract compiler**: stage 0 lax-checks `src/` using the current
   `ulib/` (via `FSTAR_LIB`) and extracts OCaml.
2. **Extract plugins**: stage 0 lax-checks the plugin modules in
   `ulib/` and extracts them.
3. **Build**: dune compiles the extracted compiler + plugins into the
   stage 1 executable.
4. **Verify ulib**: stage 1 fully verifies and extracts the standard
   library.

### Stage 2

Same structure as stage 1, but built by the stage 1 compiler.  This
is the stage that is checked for bootstrapping stability: the
`boot-diff` target re-extracts the compiler with the stage 2 compiler
and verifies that the output matches stage 2's own extracted sources.

### Stage 3

Stage 2 plus the Pulse separation logic DSL (baked-in as a plugin).
This is the compiler that is released and tested.

## Key Make targets

| Target | Description |
|---|---|
| `make build` (= `make 3`) | Build through stage 3 |
| `make 1` / `make 2` | Build stage 1 / stage 2 and set `out/` symlink |
| `make ci` | Build stage 2, run tests, boot-diff, fsharp |
| `make test` | Run tests with stage 3 |
| `make boot-diff` | Verify bootstrapping stability (stage 2 vs 2+1) |
| `make bump-stage0` | Update stage 0 snapshot from stage 2 ML files |
| `make bump-stage0-from-stage1` | Update stage 0 snapshot from stage 1 (faster) |

## Bumping stage 0

When changes to the compiler source (`src/`) or standard library
(`ulib/`) require updating the stage 0 snapshot:

```sh
make bump-stage0              # snapshot from stage 2 (full bootstrap)
make bump-stage0-from-stage1  # snapshot from stage 1 (faster)
```

The stage 1 variant is faster since it only requires building one
stage instead of two.  Both snapshot the extracted OCaml into
`stage0/` and reset `mk/fstar-01.mk` and `mk/generic-0.mk` to
match their stage 1→2 counterparts.

## Source packages

Source packages (built via `make package-src`) are self-contained
OCaml distributions that can be built without a pre-existing F\*
compiler.  They use `stage0/Makefile` (= `mk/src_package_mk.mk`)
which builds the compiler, verifies the library, and installs
everything.
