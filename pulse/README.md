# The Steel separation logic library for F*

TODO: write the corresponding Part 8 in https://fstar-lang.org/tutorial

## Current status

This repository splits Steel away from the F* code base. It
currently works with
https://github.com/FStarLang/FStar/tree/taramana_no_steel and
https://github.com/FStarLang/karamel/tree/taramana_no_steel . F*
and Karamel pull requests will be opened from those respective
branches soon.

This repository contains:
* Steel and Pulse, and their corresponding examples and tests, from F*
  master
* The Karamel extraction tests for Steel, and the Steel part of
  krmllib (currently binding the pthreads spinlock) (which we now call
  LibSteel), from Karamel master
* SteelC and its examples, from https://github.com/FStarLang/FStar/pull/2349

## Layout

This repository has been designed to closely follow the Filesystem
Hierarchy Standard (FHS), so that it can be used the same way in all
the following cases:
* direct use of the Steel repository clone
* installation into a FHS-like hierarchy (e.g. `/usr/local`)
* installation as an _opam_ package, using the _opam_ package manager for
  OCaml

In all cases, a Steel installation (or the Steel repository clone) is
laid out as follows:

* in `lib/steel`:
  * the Steel F* modules of the `Steel` and `Steel.ST` namespaces
  * the Steel F* plugin, `steel.cmxs`, containing the Steel and Pulse
    tactics, and the Steel and SteelC extraction to krml, is installed
    here
  * the LibSteel C library, `libsteel.a`, containing an implementation of
    what used to be the Steel part of krmllib (currently binding the
    pthreads spinlock), is installed here
  
* in `lib/steel/runtime`: the Steel OCaml runtime,
  `steel_runtime.cmxa`, necessary to compile and run Steel code
  extracted to OCaml, is installed here
  
* in `lib/steel/pulse`: the Pulse F* modules of the `Pulse` namespace

* in `lib/steel/c`: the SteelC F* modules of the `Steel.C` and
  `Steel.ST.C` namespaces

* in `include/steel`: the C include files necessary to compile Steel
  code extracted to C

* in `share/steel`: `Makefile.include`, the GNU Make rules to verify
  Steel code

In addition, `share/steel` also contains all examples and tests, but
those are not installed as of now.

## Prerequisites

* Z3 4.8.5 exactly
* OCaml 4.10 or higher
* GNU Make
* A GCC-compatible compiler
* F* 2023.04.15 or higher (installed via opam or via its source. A
  binary package is unlikely to work, since Steel needs to dynamically
  load a plugin.)
* Karamel, but only if you are interested in extracting to C. If you
  are only interested in verifying Steel code, or extracting to OCaml,
  then Karamel is not needed.

## Building (and optionally installing) Steel

### Building the source

1. Make sure `fstar.exe` is in your `PATH`. If F* was installed with
   opam, you may need to run `eval $(opam env)`. If F* is not in your
   `PATH`, set the `FSTAR_HOME` environment variable to the directory
   where F* was installed (or to the F* source tree), so that the F*
   executable should be in `$FSTAR_HOME/bin/fstar.exe`.
2. Run `make -j`

### Building the source and installing to a custom location

1. Follow the instructions above to build Steel from the source.
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
   
2. Build and install Steel with `opam install ./steel.opam`

## Using Steel

### Writing a Makefile to verify Steel code

Steel comes with `share/steel/Makefile.include` (which is also
properly installed by `make install` or via opam), which contains the
GNU Make rules to call F* with the Steel include path and the Steel
plugin loaded.

1. Make sure `fstar.exe` is in your `PATH`. If F* was installed with
   opam, you may need to run `eval $(opam env)`. Alternatively,
   instead of having F* in your `PATH`, you can also set the
   `FSTAR_HOME` environment variable to the directory where F* was
   installed (or to the F* source tree), so that the F* executable
   should be in `$FSTAR_HOME/bin/fstar.exe`.

2. Define the `STEEL_HOME` environment variable. This should be one of the following:
   * If used directly from source: The root directory of your clone of the Steel repository
   * If installed with `make install`: The PREFIX directory used when installing Steel
   * If installed with `opam`: The prefix directory of the opam
     switch where Steel was installed, obtained with `opam config var prefix`
 
3. (Optional) In your Makefile, define the following variables with `+=` or `:=` :
   * `FSTAR_FILES`: some more F* files to verify, in addition to the
     `*.fst` and `.fsti` files of your project
   * `EXCLUDE_FILES`: some F* to skip for verification
   * `FSTAR_OPTIONS`: additional options to pass to F*. While
     `Makefile.include` is already configured to use Steel, you need
     to add more options if you need Pulse and/or SteelC:
     * if you want to use Pulse, add `--include $STEEL_HOME/lib/steel/pulse`
     * if you want to use SteelC, add `--include $STEEL_HOME/lib/steel/c`

4. After those variable definitions, insert `include
   $STEEL_HOME/share/steel/Makefile.include` to your Makefile.

5. In your project directory, run `make -j verify`

### Calling F* directly

If you already have an existing `Makefile` for your Steel-based
project, you now need to pass new options to your Makefile to use
Steel from this repository, as described in this section.

To call F* with Steel:

1. Make sure F* and Steel are properly located, following steps 1 and 2 above.
2. Pass the following options to F*:
   * in all cases, `--include $STEEL_HOME/lib/steel --load_cmxs steel`
   * if you want to use Pulse, add `--include $STEEL_HOME/lib/steel/pulse`
   * if you want to use SteelC, add `--include $STEEL_HOME/lib/steel/c`

TODO: we should distribute a binary package with the Steel plugin
statically linked in fstar.exe. In that case, the `--load_cmxs steel`
option to load the Steel plugin would no longer be necessary. Then,
what about the `--include` paths?

### Extracting Steel code to C or OCaml

TODO: add instructions to extract code. Meanwhile, see:
* `share/steel/examples/steel/llist2/Makefile` for a C extraction
  example. (The rule to extract `*.krml` files is already in the
  `share/steel/Makefile.include` file distributed and installed with
  Steel.)
* `share/steel/examples/steel/OWGCounter` for an OCaml extraction
  example. This example has both a `Makefile` to extract the Steel
  code to C, and a `dune` file to compile the extracted OCaml
  code. Most notably, to compile and run OCaml code extracted from
  Steel, `$STEEL_HOME` has to be added to `OCAMLPATH` (which is
  already the case by default with opam, if the opam environment is
  properly set up with `eval $(opam env)`), and the `steel.runtime`
  package has to be used.

## Developer's guide

If you want to contribute to Steel, Pulse or SteelC code, please read
`CONTRIBUTING.md`
