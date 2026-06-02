# Building and installing `fstar.lib`

This directory contains the OCaml *sources* of the F\* application library
`fstar.lib`:

  * `app/`      – handwritten OCaml realizations of the F\* library primitives;
  * `app-extra/`– handwritten realizations that depend on extracted modules;
  * `ulib.ml/`  – the F\*-extracted OCaml modules of the standard library (`ulib`);

together with a `dune`/`dune-project` to build and install them.

Unlike older binary packages, this package deliberately does **not** ship a
precompiled `fstar.lib`. Instead, you build it yourself against your own OCaml
toolchain, which avoids OCaml ABI mismatches between the package and your
compiler/findlib setup.

## Prerequisites

An OCaml toolchain with `dune` and the following findlib packages (all available
via opam): `batteries`, `zarith`, `stdint`, `pprint`, `ppx_deriving`,
`ppx_deriving_yojson`.

## Build and install

From this directory:

```
./install.sh
```

(Optionally pass an install prefix and libdir: `./install.sh <prefix> <libdir>`;
they default to `opam var prefix` and `opam var lib`.)

This installs `fstar.lib` as a findlib package into your current opam switch, so
that `ocamlfind query fstar.lib` resolves and OCaml code extracted by F\* can be
compiled against it.

### Why not a bare `dune install`?

`fstar.lib` is the `lib` sub-package of the findlib package `fstar`, which also
provides `fstar.compiler` and `fstar.pluginlib` (the latter is used by
`fstar.exe --ocamlopt_plugin`). dune writes the package metadata at
`<libdir>/fstar/META` and offers no option to merge or skip it, so a bare
`dune install` of this project would **overwrite** that file with a META that
mentions only `lib`, silently dropping the `compiler`/`pluginlib` stanzas and
breaking plugin compilation. `install.sh` performs the `dune install` and then
merges the freshly generated `lib` stanza back into the pre-existing META,
preserving every other sub-package.
