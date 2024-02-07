# The Steel and Pulse separation logic system for F*

## Contents of this package

This binary package contains z3 4.8.5, F*, Karamel, Steel, Pulse, and
(except on Windows) Pulse2Rust:

* in `bin`: the executables for z3, F* and Karamel

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
  (except `Pulse.Lib`)

* in `lib/steel/c`: the SteelC F* modules of the `Steel.C` and
  `Steel.ST.C` namespaces

* in `include/steel`: the C include files necessary to compile Steel
  code extracted to C

* in `share/steel`: `Makefile.include`, the GNU Make rules to verify
  Steel and Pulse code
  
* in `share/steel/examples/pulse`:
  * in `lib`: the Pulse user library files (namespace `Pulse.Lib`)
  * in `_output/cache`: the corresponding `.checked` files

* in `pulse2rust`: the executable for Pulse2Rust. (Absent from the
  Windows binary package)

## Using Steel and Pulse

### Writing a Makefile to verify Steel or Pulse code

Steel and Pulse come with `share/steel/Makefile.include`, which contains the
GNU Make rules to call F* with the Steel include path and the Steel/Pulse
plugin loaded.

1. Make sure the `bin` subdirectory is in your `PATH`.

2. Define the `PULSE_HOME` environment variable to the root directory
   of this package.

3. (Optional) In your Makefile, define the following variables with `+=` or `:=` :
   * `FSTAR_FILES`: some more F* files to verify, in addition to the
     `*.fst` and `.fsti` files of your project
   * `EXCLUDE_FILES`: some F* to skip for verification
   * `FSTAR_OPTIONS`: additional options to pass to F*. While
     `Makefile.include` is already configured to use Steel, you need
     to add more options if you need Pulse and/or SteelC:
     * if you want to use Pulse, add `--include $PULSE_HOME/lib/steel/pulse`
     * if you want to use SteelC, add `--include $PULSE_HOME/lib/steel/c`
   * `FSTAR_DEP_OPTIONS`: additional options to pass to F* to compute
     dependencies (in addition to `FSTAR_OPTIONS`), such as `--extract`
   * `FSTAR_ML_CODEGEN`: useful only if you want to extract OCaml
     code. If you want to extract a F* plugin, set this option to
     `Plugin`. Otherwise, it is set by default to `OCaml`.

4. After those variable definitions, insert `include
   $PULSE_HOME/share/steel/Makefile.include` to your Makefile.

5. In your project directory, run `make -j verify`

### Calling F* directly

If you already have an existing `Makefile` for your Steel- or
Pulse-based project, you now need to pass new options to your Makefile
to use Steel from this repository, as described in this section.

To call F* with Steel or Pulse, pass the following options to F*:
* in all cases, `--include $PULSE_HOME/lib/steel --load_cmxs steel`
* if you want to use Pulse, add `--include $PULSE_HOME/lib/steel/pulse`
* if you want to use SteelC, add `--include $PULSE_HOME/lib/steel/c`
