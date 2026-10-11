# Compilation targets

A module can have several implementations (and interfaces), one per
*target*.  The target is written after a dash in the file name:

    FStar.HashTable.fsti          common interface
    FStar.HashTable-model.fst     pure model implementation
    FStar.HashTable-ocaml.fst     OCaml implementation
    FStar.HashTable-c.fst         C implementation

A target name matches `[a-z][a-z0-9_]*`.  All of these files declare
`module FStar.HashTable`.  Files without a target are *common* files.

## Visibility

- A common file sees only common files.
- A file for target `t` sees common files and other files for target `t`.
  When it resolves a module `M`, it looks for `M-t` first and then for `M`.

So `A-foo.fst` can never be a dependency of `B-bar.fst` or `C.fst`, but
`B-foo.fst` can depend on, or friend, `A-foo.fst`.

## Rules

- A module may not have both a common implementation and a target-specific
  one (`A.fst` together with `A-ocaml.fst`).  The same applies to
  interfaces.  Either case is a hard error.
- `friend A` in a common file requires `A.fst`.  `friend A` in a file for
  target `t` requires `A.fst` or `A-t.fst`.
- Checked files keep the target: `A-ocaml.fst.checked`.

## Verification and extraction

`fstar.exe --dep full *.fst*` lists every target, so verifying all of its
files checks each implementation, including the model ones.

Extraction picks the target from `--codegen`:

| `--codegen`   | target  |
|---------------|---------|
| `OCaml`       | `ocaml` |
| `Plugin`      | `ocaml` |
| `FSharp`      | `fsharp`|
| `C`, `KrmlC`  | `c`     |
| `KrmlRust`    | `rust`  |

The two C printers share the `-c` files.

`--codegen Plugin A-ocaml.fst` builds the plugin for module `A` (unit `A`,
loaded with `--load_cmxs A`).  IDE module completion lists module names
without the target and only offers modules visible from the current file.

There is no fallback yet: a module with only target-specific implementations
cannot be extracted for a target it lacks.  See `tests/targets`.
