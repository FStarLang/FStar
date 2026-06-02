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

The simplest way is to let `fstar.exe` do it for you (it runs exactly the steps
below and refuses if it would overwrite an existing `fstar` findlib package):

```
fstar.exe --install_lib
```

Alternatively, from this directory:

```
dune build
dune install
```

`dune install` (with no `--prefix`) installs into your current opam switch, so
that `ocamlfind query fstar.lib` resolves and OCaml code extracted by F\* can be
compiled against it.

### Caveat: an existing `fstar` findlib package

`fstar.lib` is the `lib` sub-package of the findlib package `fstar`, which may
also provide `fstar.compiler` and `fstar.pluginlib` (the latter is used by
`fstar.exe --ocamlopt_plugin`). dune writes the package metadata at
`<libdir>/fstar/META` and offers no option to merge or skip it, so a bare
`dune install` of this project into a switch that *already* has the `fstar`
package would **overwrite** that file with a META mentioning only `lib`,
silently dropping the `compiler`/`pluginlib` stanzas.

To avoid this, install `fstar.lib` into a switch that does not already provide
the `fstar` package — which is exactly what `fstar.exe --install_lib` enforces.
