# Compilation targets

A module can have several interfaces and implementations, each with a
*tag* written after the first dash of the file name:

    Uart.fsti                common interface
    Uart.fst                 fallback implementation
    Uart-model.fst           pure model implementation
    Uart-s2.fst              for any S2 board
    Uart-s2.qemu.fst         for S2 under QEMU
    Uart-s3-c.fst            for S3 boards, extracted to C

All of these files declare `module Uart`.  Files without a tag are *common*
files.

## Tags

A tag is a set of *atoms* separated by `-`.  An atom is a dotted path of
names matching `[a-z][a-z0-9_]*`.  Atoms are hierarchical: `s2.qemu`
implies `s2`.  The order of the atoms does not matter, so `Uart-c-s3.fst`
and `Uart-s3-c.fst` have the same tag (and may not coexist).  Atoms do not
have to be declared anywhere.

A tag `T` *implies* a tag `U` if every atom of `U` is implied by an atom of
`T`.  The empty tag (a common file) is implied by every tag.

## Selection

A file `F` with tag `T` that refers to module `M` sees, separately for the
interface and for the implementation, the most specific file of `M` whose
tag is implied by `T`.  Common files are the fallback.  If several files
apply and none of them is more specific than the others (say `Amb-c.fst`
and `Amb-s2.fst`, seen from `UseAmb-c-s2.fst`), that is an error; add a
file whose tag combines theirs (`Amb-c-s2.fst`).

Only the interface is used, unless `M` has no interface or `F` friends `M`.
A file can only friend a module if an implementation applies to it.

## Stability

Every file is verified once, for its own tag, but is extracted for any
configuration that implies its tag.  So the files it sees must be the same
in all those configurations.  It is an error if a file uses a file of `M`
while a strictly more specific file of `M` (of the same kind) exists whose
tag is *compatible* with `T`.  Two tags are incompatible only if they have
atoms that diverge below a common root: `s2.qemu` and `s2.silicon` are
incompatible, while `s2` and `s3`, or `s2` and `c`, are compatible.

For example, with `Uart-s2.fst` and `Uart-s2.qemu.fst` but no `Uart.fsti`,
`Spy-s2.fst` cannot use `Uart`: verification would see `Uart-s2.fst`, but
extraction for `s2.qemu` would use `Uart-s2.qemu.fst`.  With a common
`Uart.fsti`, `Spy-s2.fst` only sees the interface and is fine (unless it
friends `Uart`).  `Spy-s2.silicon.fst` may friend `Uart`: the `s2.qemu`
file is incompatible with its tag.

The rule also applies to the interface of the file's own module.

## Verification and extraction

`fstar.exe --dep full *.fst*` lists all the files, so verifying all of them
checks every implementation, including the model ones.  Checked files keep
the tag: `Uart-s2.fst.checked`.

Extraction uses the configuration given by `--target <tag>` together with
an atom for the language, picked from `--codegen`:

| `--codegen`   | atom     |
|---------------|----------|
| `OCaml`       | `ocaml`  |
| `Plugin`      | `ocaml`  |
| `FSharp`      | `fsharp` |
| `C`, `KrmlC`  | `c`      |
| `Cherry`      | `c.cherry` |
| `KrmlRust`    | `rust`   |

For example, `--codegen C --target s3.silicon` extracts in configuration
`s3.silicon-c`, and selects `Uart-s3-c.fst` above.  Cherry extends the C
backend, so it uses the `c` files unless a `c.cherry` file is more specific.  Because of the
stability rule, no further checks are needed at extraction time.

`--codegen Plugin A-ocaml.fst` builds the plugin for module `A` (unit `A`,
loaded with `--load_cmxs A`).  IDE module completion lists module names
without the tag and only offers modules visible from the current file.

See `tests/targets`.

## Models in the libraries

An interface without an implementation is just a list of axioms.  So every
`.fsti` in `ulib/` and `pulse/lib/` must come with an implementation: an
`.fst` when it is extracted, or otherwise (e.g. when the implementation is
native) a `-model.fst` showing that the interface is consistent.  Model
implementations must not use `assume`, `admit`, etc.  This is checked in CI
by `make check-fsti-impls` (`.scripts/check_fsti_impls.py`), and the
remaining exceptions are listed in `.scripts/fsti_without_impl.txt`.
