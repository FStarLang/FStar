Hello F\*
========

Sample projects demonstrating F\* verification and OCaml extraction using dune.

# Prerequisites

- An F\* installation (provides `fstar.exe`)
- OCaml toolchain with opam
- dune (≥ 3.15)
- The `fstar.lib` opam package (F\* OCaml support library)

# Projects

## Hello

A single-file example: verifies `Hello.fst` and extracts it to OCaml.

```
dune exec Hello/Hello.exe
```

## multifile

A multi-module example with `A.fst`, `B.fst`, and `Main.fst` demonstrating
inter-module dependencies.

```
dune exec multifile/Main.exe
```

# How it works

Each project uses `--dep dune` to generate dependency rules in two phases:

1. **Build phase** (`--output_ext fst.checked`): verifies `.fst` files → `.fst.checked`
2. **Extract phase** (`--output_ext ml --codegen OCaml`): extracts checked files → `.ml`

The generated rules are dynamically included into each project's `dune` file.
The `(executable ...)` stanza then compiles the extracted OCaml into a native binary.
