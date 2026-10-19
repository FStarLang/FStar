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

Each project uses `--dep dune --output_ext fst.checked` to generate the rules
that verify its `.fst` files into `.fst.checked` files. The generated rules
are dynamically included into each project's `dune` file.

Extraction is a single rule in each project's `dune` file: F\* compiles the
whole program, starting from its entry module, into one OCaml file
(`--codegen OCaml --custard_entry_module Main -o Main.ml`). The
`(executable ...)` stanza then compiles it into a native binary.
