# The Pulse separation logic DSL for F*

For documentation on how to use Pulse, see https://fstar-lang.org/tutorial/book/pulse/pulse.html#pulse-proof-oriented-programming-in-concurrent-separation-logic

## Layout

This repository has been designed to closely follow the Filesystem
Hierarchy Standard (FHS), so that it can be used the same way in all
the following cases:
* direct use of the Pulse repository clone
* installation into a FHS-like hierarchy (e.g. `/usr/local`)
* installation as an _opam_ package, using the _opam_ package manager for
  OCaml

In all cases, a Pulse installation (or the Pulse repository clone) is
laid out as follows:

* in `lib/`:
  * the theoretical foundations of Pulse, in `core/` (namespace `PulseCore`)
  * the interface powering the Pulse DSL, `common/Pulse.Main.fsti`
  * the Pulse standard library, in `pulse/` (namespace `Pulse.Lib`), with
    some subdirectories for typeclasses (in `class`, namespace
    `Pulse.Class`) and pledges (in `pledge`), and for the OCaml
    runtime implementation of Pulse references, etc. (in `ml`)
  * the Pulse F* plugin, `pulse.cmxs`, containing the Pulse
    tactics, and the Pulse and PulseC extraction to krml, is installed
    here
  * the PulseC F* modules of the `Pulse.C` namespace (in `c`)

* in `share/pulse`: `Makefile.include`, the GNU Make rules to verify
  Pulse code

In addition, `share/pulse/examples` also contains all examples and
tests, but those are not installed as of now.

The only exception is Pulse2Rust, which is still in its own directory,
and is not installed as of now, due to its dependency on the Rust
toolchain.

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

## Building (and optionally installing) Pulse

### Building the source

1. Make sure `fstar.exe` is in your `PATH`. If F* was installed with
   opam, you may need to run `eval $(opam env)`. If F* is not in your
   `PATH`, set the `FSTAR_HOME` environment variable to the directory
   where F* was installed (or to the F* source tree), so that the F*
   executable should be in `$FSTAR_HOME/bin/fstar.exe`.
2. Run `make -j`

### Building the source and installing to a custom location

1. Follow the instructions above to build Pulse from the source.
2. Install with `PREFIX=<your prefix> make -j install` . By default,
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

### Writing a Makefile to verify Pulse code

Pulse comes with `share/pulse/Makefile.include` (which is also
properly installed by `make install` or via opam), which contains the
GNU Make rules to call F* with the Pulse include path and the Pulse
plugin loaded.

1. Make sure `fstar.exe` is in your `PATH`. If F* was installed with
   opam, you may need to run `eval $(opam env)`. Alternatively,
   instead of having F* in your `PATH`, you can also set the
   `FSTAR_HOME` environment variable to the directory where F* was
   installed (or to the F* source tree), so that the F* executable
   should be in `$FSTAR_HOME/bin/fstar.exe`.

2. Define the `PULSE_HOME` environment variable. This should be one of the following:
   * If used directly from source: The root directory of your clone of the Pulse repository
   * If installed with `make install`: The PREFIX directory used when installing Pulse
   * If installed with `opam`: The prefix directory of the opam
     switch where Pulse was installed, obtained with `opam config var prefix`
 
3. (Optional) In your Makefile, define the following variables with `+=` or `:=` :
   * `SRC_DIRS`: the directories containing the source `.fst` and
     `.fsti` files of your project, in addition to the current
     directory.
   * `FSTAR_FILES`: the F* files to verify. By default, those are the
     `*.fst` and `*.fsti` files from the directories in `SRC_DIRS`
   * `INCLUDE_PATHS`: the paths to include for verification with F*'s
     `--include` option. By default, those are the Pulse library
     include paths and `SRC_DIRS`.
     * If you want to use PulseC, add `$PULSE_HOME/lib/pulse/c` to
       this variable.
   * `ALREADY_CACHED_LIST`: the comma-separated list of namespaces
     that are assumed to be already cached. By default
     `Prims,FStar,PulseCore,Pulse`, but if all of your source files
     are in the same namespace, you can override this variable with
     something like `*,-MyNamespace`
   * `OTHERFLAGS`: additional options to pass to F*.
   * `FSTAR_DEP_OPTIONS`: additional options to pass to F* to compute
     dependencies (in addition to `FSTAR_OPTIONS`), such as `--extract`
   * `FSTAR_ML_CODEGEN`: useful only if you want to extract OCaml
     code. If you want to extract a F* plugin, set this option to
     `Plugin`. Otherwise, it is set by default to `OCaml`.

4. After those variable definitions, insert `include
   $PULSE_HOME/share/pulse/Makefile.include` to your Makefile.

5. In your project directory, run `make -j verify`

### Calling F* directly

If you already have an existing `Makefile` for your Pulse-based
project, you now need to pass new options to your Makefile to use
Pulse from this repository, as described in this section.

To call F* with Pulse:

1. Make sure F* and Pulse are properly located, following steps 1 and 2 above.
2. Pass the following options to F*:
   * in all cases, `--include $PULSE_HOME/lib/pulse`
   * if you want to use PulseC, add `--include $PULSE_HOME/lib/pulse/c`

### Extracting Pulse code to C or OCaml

The rule to extract `*.krml` files is already in the
`share/pulse/Makefile.include` file distributed and installed with
Pulse. To learn how to run Karamel, you can have a look at the
PulseCPointStruct example in `share/pulse/examples/Makefile`.

The rule to extract `*.ml` files is already in the
`share/pulse/Makefile.include` file distributed and installed with
Pulse. TODO: add a compilation example for OCaml.

## Developer's guide

If you want to contribute to Pulse, please read `CONTRIBUTING.md`
