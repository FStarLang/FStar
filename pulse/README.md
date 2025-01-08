# The Pulse separation logic DSL for F*

For documentation on how to use Pulse, see https://fstar-lang.org/tutorial/book/pulse/pulse.html#pulse-proof-oriented-programming-in-concurrent-separation-logic

## Prerequisites

* Z3 4.13.3 (exactly this version)
* OCaml 4.10 or higher
* GNU Make
* A GCC-compatible compiler
* F* 2023.04.15 or higher (installed via opam or via its source. A
  binary package is unlikely to work, since Pulse needs to dynamically
  load a plugin.)
* Karamel, but only if you are interested in extracting to C. If you
  are only interested in verifying Pulse code, or extracting to OCaml,
  then Karamel is not needed.
* Rust and the bindgen-cli crate are required to build pulse2rust.
  If you would like to skip this, set the environment variable
  `PULSE_NO_RUST` to something non-empty.

## Building (and optionally installing) Pulse

### Building the source

1. Make sure `fstar.exe` is in your `PATH`. If F* was installed with
   opam, you may need to run `eval $(opam env)`. If F* is not in your
   `PATH`, set the `FSTAR_EXE` environment variable to the location
   of fstar.exe.
2. Run `make` (possibly with `-j`). This will generate a local
   installation under the `out/` subdirectory, identical to the ones
   created by the other options below.

### Building the source and installing to a custom location

1. Follow the instructions above to build Pulse from the source.
2. Install with `PREFIX=<your prefix> make install` . By default,
   `PREFIX` will be set to `/usr/local`, as per the UNIX custom.

### Building and installing with opam

1. Clone the F* repository and install F* with `opam install
   <path to FStar>/./fstar.opam`. This will build F* and all of its
   dependencies (including Z3)
   
   (Right now the F* release on the opam package repository is too
   old. Once version 2023.04.15 or later is made available on the opam
   repository, cloning the F* repository will no longer be necessary,
   and `opam install fstar` should be enough for this step.)
   
2. Build and install Pulse with `opam install ./pulse.opam`

## Using Pulse

In your F* project, simply add `--include XYZ/lib/pulse` to your
Makefile invocations (and possibly VS code configs), where `XYZ` is the
location where Pulse was installed (depending on the alternatives above,
e.g. it would be `$PWD/out` for a local install).

Pulse consists of both an F* plugin and a library. F* will automatically
attempt to load the Pulse plugin whenever required, that is when a `#lang-pulse`
directive is processed. The checked files are also under that directory, and
are automatically picked up.

## Developer's guide

If you want to contribute to Pulse, please read `CONTRIBUTING.md`
