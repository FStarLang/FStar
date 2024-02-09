# The Pulse separation logic DSL for F*

## Contents of this package

This binary package contains z3 4.8.5, F*, Karamel, Pulse, and
(except on Windows) Pulse2Rust:

* in `bin`: the executables for z3, F* and Karamel

* in `lib/pulse`:
  * the Pulse F* plugin, `pulse.cmxs`, containing the Pulse checker,
    and the Pulse and PulseC extraction rules to krml, is installed
    here
  * the Pulse standard library, of the `Pulse` and `PulseCore`
    namespaces (including PulseC's `Pulse.C`)

* in `share/pulse`: `Makefile.include`, the GNU Make rules to verify
  Pulse code

* in `pulse2rust`: the executable for Pulse2Rust. (Absent from the
  Windows binary package)

## Using Pulse

### Writing a Makefile to verify Steel or Pulse code


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
   * in all cases, `--include $PULSE_HOME/lib/pulse --include $PULSE_HOME/lib/pulse/core --include $PULSE_HOME/lib/pulse/class  --include $PULSE_HOME/lib/pulse/pledge --load_cmxs pulse`
   * if you want to use PulseC, add `--include $PULSE_HOME/lib/pulse/c`
