# F* Build System Architecture

This diagram shows how the multi-stage build produces fstar.exe.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           F* BUILD PIPELINE                                  │
└─────────────────────────────────────────────────────────────────────────────┘

  ┌──────────────────────────────────────────────────────────────────────────┐
  │ STAGE 0: Bootstrap Compiler                                              │
  │ ┌─────────────────────────┐                                              │
  │ │ stage0/dune/fstar-guts/ │  Pre-generated OCaml snapshot                │
  │ │ ├── FStarC_*.ml         │  (committed to repo, updated via bump-stage0)│
  │ │ └── *.mly parsers       │                                              │
  │ └────────────┬────────────┘                                              │
  │              │ dune build --root=stage0/dune                             │
  │              ▼                                                           │
  │ ┌─────────────────────────┐                                              │
  │ │ stage0/out/bin/fstar.exe│  Bootstrap compiler (can run F* code)       │
  │ └────────────┬────────────┘                                              │
  └──────────────┼────────────────────────────────────────────────────────────┘
                 │
                 │ FSTAR_EXE=stage0/out/bin/fstar.exe
                 ▼
  ┌──────────────────────────────────────────────────────────────────────────┐
  │ EXTRACTION: F* Sources → OCaml                                           │
  │                                                                          │
  │ ┌─────────────────────┐     fstar.exe --codegen OCaml    ┌─────────────┐ │
  │ │ src/fstar/FStarC.*.fst│ ──────────────────────────────► │src/extracted│ │
  │ │ (F* compiler sources)│                                 │ FStarC_*.ml │ │
  │ └─────────────────────┘                                  └──────┬──────┘ │
  │                                                                 │        │
  │ dune build @extract-stage1                                      │        │
  └─────────────────────────────────────────────────────────────────┼────────┘
                                                                    │
                 ┌──────────────────────────────────────────────────┘
                 │
                 ▼
  ┌──────────────────────────────────────────────────────────────────────────┐
  │ STAGE 1: Compiler Library                                                │
  │                                                                          │
  │ ┌─────────────────────┐     ┌─────────────────────┐                      │
  │ │ src/extracted/      │     │ ulib/ml/            │                      │
  │ │ FStarC_*.ml         │  +  │ FStar_*.ml          │  (runtime support)   │
  │ └─────────┬───────────┘     └─────────┬───────────┘                      │
  │           │                           │                                  │
  │           └─────────────┬─────────────┘                                  │
  │                         │ ocamlfind / dune                               │
  │                         ▼                                                │
  │           ┌─────────────────────────┐                                    │
  │           │ fstarcompiler_stage1.cma│  Compiler as library               │
  │           └─────────────┬───────────┘                                    │
  │                         │                                                │
  │ dune build @stage1      │                                                │
  └─────────────────────────┼────────────────────────────────────────────────┘
                            │
                            │
                            ▼
  ┌──────────────────────────────────────────────────────────────────────────┐
  │ PLUGINS: Tactics & Extensions                                            │
  │                                                                          │
  │ ┌─────────────────────────────────────────────────────────────────────┐  │
  │ │ ulib/FStar.Tactics.*.fst  ──extract──►  src/tactics/FStarC_*.ml     │  │
  │ │ ulib/FStar.Class.*.fst    ──extract──►  src/plugins/FStarC_*.ml     │  │
  │ └─────────────────────────────────────────────────────────────────────┘  │
  │                                                                          │
  │                         │ ocamlfind / dune                               │
  │                         ▼                                                │
  │           ┌─────────────────────────┐                                    │
  │           │ fstar_plugins_stage1.cma│  Plugin modules                    │
  │           └─────────────┬───────────┘                                    │
  │                         │                                                │
  │ (built as part of @stage1)                                               │
  └─────────────────────────┼────────────────────────────────────────────────┘
                            │
                            │
                            ▼
  ┌──────────────────────────────────────────────────────────────────────────┐
  │ STAGE 2: Final Executable                                                │
  │                                                                          │
  │ ┌───────────────────────┐   ┌────────────────────────┐                   │
  │ │fstarcompiler_stage1.cma│ + │fstar_plugins_stage1.cma│                   │
  │ └───────────┬───────────┘   └───────────┬────────────┘                   │
  │             │                           │                                │
  │             └─────────────┬─────────────┘                                │
  │                           │ ocamlfind -linkall                           │
  │                           ▼                                              │
  │             ┌─────────────────────────┐                                  │
  │             │   fstar.exe (FINAL)     │  Full compiler with plugins      │
  │             │ _build/default/src/     │                                  │
  │             │   stage2/fstar.exe      │                                  │
  │             └─────────────────────────┘                                  │
  │                                                                          │
  │ dune build @stage2                                                       │
  └──────────────────────────────────────────────────────────────────────────┘


  ┌──────────────────────────────────────────────────────────────────────────┐
  │ ULIB: Standard Library (verified with fstar.exe)                         │
  │                                                                          │
  │ ┌─────────────────────────────────────────────────────────────────────┐  │
  │ │ ulib/                                                               │  │
  │ │ ├── FStar.Pervasives.fsti    Core primitives                        │  │
  │ │ ├── FStar.List.fst           List operations                        │  │
  │ │ ├── FStar.Seq.fst            Sequences                              │  │
  │ │ ├── FStar.Map.fst            Maps                                   │  │
  │ │ ├── FStar.Tactics.*.fst      Tactic library                         │  │
  │ │ ├── FStar.Class.*.fst        Type classes                           │  │
  │ │ └── ...                      (~200 modules)                         │  │
  │ └─────────────────────────────────────────────────────────────────────┘  │
  │                                                                          │
  │ Checked by fstar.exe to produce .checked files                           │
  │ Extracted to OCaml for plugins (tactics, typeclasses)                    │
  └──────────────────────────────────────────────────────────────────────────┘


  ┌──────────────────────────────────────────────────────────────────────────┐
  │ KEY DUNE ALIASES                                                         │
  │                                                                          │
  │   make stage0    →  dune build --root=stage0/dune                        │
  │   make extract   →  dune build @extract-stage1  (needs FSTAR_EXE)        │
  │   make stage1    →  dune build @stage1                                   │
  │   make stage2    →  dune build @stage2                                   │
  │   make build     →  all of the above in sequence                         │
  │   make test      →  dune runtest                                         │
  └──────────────────────────────────────────────────────────────────────────┘
```

## Build Flow Summary

1. **Stage 0**: Compile pre-generated OCaml snapshot → bootstrap `fstar.exe`
2. **Extract**: Use bootstrap compiler to extract F* sources to fresh OCaml
3. **Stage 1**: Compile extracted OCaml + ulib/ml → compiler library
4. **Plugins**: Extract & compile tactics/typeclasses → plugin library  
5. **Stage 2**: Link compiler + plugins → final `fstar.exe`

## Why Multi-Stage?

F* is **self-hosted** - the compiler is written in F*. To build it:
- We need an F* compiler to compile F* code
- Stage0 provides this bootstrap (committed OCaml snapshot)
- Extraction produces fresh OCaml from current F* sources
- This ensures the compiler can always be rebuilt from source

## Directory Structure

```
fstar-dune/
├── stage0/                    # Bootstrap compiler
│   ├── dune/                  # Dune project for stage0
│   │   └── fstar-guts/        # Pre-generated OCaml sources
│   └── out/bin/fstar.exe      # Built bootstrap compiler
│
├── src/
│   ├── fstar/                 # F* compiler sources (.fst files)
│   ├── extracted/             # Generated OCaml from extraction
│   ├── stage1/                # Stage1 compiler library build
│   ├── stage2/                # Final executable build
│   ├── tactics/               # Tactic plugin sources
│   └── plugins/               # Other plugin sources
│
├── ulib/                      # F* standard library
│   ├── FStar.*.fst/fsti       # Library modules
│   └── ml/                    # OCaml runtime support
│
├── _build/                    # Dune build output
│   └── default/src/stage2/
│       └── fstar.exe          # FINAL OUTPUT
│
├── Makefile                   # User-facing build commands
├── dune                       # Root dune config
├── dune-project               # Dune project definition
└── fstar.opam                 # OCaml package dependencies
```
