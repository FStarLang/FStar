# Developer's guide

This section is useful only if you want to contribute to Steel, Pulse
or SteelC code.

In all cases (user or developer), please first read `README.md`

## Source layout

* In `src/c`: The handwritten LibSteel library for C (currently
  binding the pthreads spinlock)
* In `src/extraction`: The krml extraction rules for Steel and
  SteelC. This F* code typechecks against the F* sources.
* In `src/syntax-extension`: A top-level parser hook for the custom
  syntax of pulse. This F* code typechecks against the F* sources.
* In `src/ocaml/runtime`: The handwritten Steel runtime library for
  OCaml. This OCaml code typechecks and compiles against the
  `fstar.lib` package.
* In `src/ocaml/plugin/generated`: A snapshot of the generated OCaml
  code for the Steel plugin, containing the extracted implementations
  of the Steel and Pulse tactics and the Steel and SteelC extraction
  to krml.
* In `src/proofs/steelc`: The F* correctness proofs of the SteelC
  library, i.e. the `*.fst` implementations of the
  `lib/steel/c/Steel.ST.C.*.fsti` interfaces. Those files are not
  necessary for the end-user, and they take a large amount of time and
  memory to verify.

## Modifying the specifications and proofs

If you want to modify the specs and proofs, or add a new module, as
long as you do not modify the tactics, you can work directly in
`lib/steel` and its subdirectories. While you can reverify Steel
directly with `make` from the Steel root directory, you can also use
the partial Makefiles from `lib/steel`, `lib/steel/c` and
`lib/steel/pulse` to verify only those parts that you are modifying.

## Modifying the Steel interfaces of the LibSteel C library

However, if you modify the Steel interfaces to the LibSteel C library
from `src/c` (currently the spinlock implementation with pthreads, for
`Steel.SpinLock`), you need to regenerate the corresponding C header
files to `include/steel/*.h`.

To do so, you first need to clone and compile Karamel, and set the
`KRML_HOME` variable to your Karamel clone.

Then, you can run `make -j -C src extract-c` . You can then recompile
LibSteel with `make` from the Steel root directory.

## Modifying the Steel or Pulse tactics

If you modify the Steel (resp. Pulse) tactic, you need to regenerate
the corresponding OCaml snapshot. To this end, you can do `make -j -C
src extract-steel-plugin` (resp. `make -j -C src
extract-pulse-plugin`). Then you can compile the obtained plugin and
reverify Steel and Pulse with it, by simply running `make` from the
Steel root directory.

### Notes on the implementation of Pulse

The Pulse checker is an F* program implemented as a plugin to the F*
compiler. The sources of the core part of the plugin is in
lib/steel/pulse in files named Pulse.Checker.* but also Pulse.Typing,
Pulse.Soundness. Maybe all of these should move under the
Pulse.Checker namespace to make it clear that they are not
user-facing.

Pulse also provides custom syntax, and this is implemented as a
OCaml/Menhir parser in src/ocaml/plugin, which builds an AST in
src/syntax_extension/PulseSugar.fst

The surface syntax parsed by the parser above is desugared to the the
Pulse AST using the code in src/syntax_extension/PulseDesugar.fst


Phases of the Pulse checker:

1. menhir parser produces PulseSugar

2. PulseDesugar transforms PulseSugar to Pulse.Syntax.Base (in lib/steel/pulse)

3. Pulse.Main is the main Pulse checker, and it typechecks the
   Pulse.Syntax.Base AST and transforms it into FStar.Reflection.Data,
   the syntax of F* terms and their typing derivations.

4. The F* compiler then processes this as usual


## Modify the Steel or SteelC extraction rules, or the syntax extension.

If you modify the Steel or SteelC extraction rules in `src/extraction`
(`ExtractSteel.fst` and `ExtractSteelC.fst` respectively), you need to
regenerate the corresponding OCaml snapshot.

To do so, you need to clone the F* repository and set the `FSTAR_HOME`
variable to your F* clone. Indeed, the extraction rules typecheck
against the F* sources. An opam installation of F* (or a binary
package) will not work.

Then, you can extract the rules with `make -j -C src
extract-extraction` . Then you can recompile everything with `make`
from the Steel root directory.

Likewise, if you modify the syntax extension, you should run `make -j
-C src extract-syntax-extension`

## Safe rules to regenerate and recompile everything

If you don't know in advance the impact of your changes, you can
simply run `make -j -C src full-boot` . This will re-extract and
recompile everything.

To use this rule, you need:
* a clone of Karamel, with the `KRML_HOME` variable pointed to it
* a clone of the F* sources, with the `FSTAR_HOME` variable pointed to
  it

However, this rule will not reverify the proofs from `src/proofs`,
which basically have no impact on the user code. These proofs take
very long time and high amounts of memory to verify.

## Testing

`share/steel` contains all examples and tests. You can run `make -j -C
share/steel` to verify and test them. This rule will work whether you have
Karamel or not. If you have Karamel, then this rule will also extract
and compile (and sometimes run) C extraction examples. Alternatively,
you can run `make -j test` from the Steel root directory, which will
build Steel beforehand.

If you have Docker, you can run `docker build -f
src/ci/opam.Dockerfile .` to test the opam installation of Steel
(including all dependencies.) This will also verify all examples and
tests, by moving them outside of the Steel directory hierarchy
beforehand, to make sure that the location of those examples does not
need to depend on the location of Steel.

Finally, you can run `make -j -C src ci` to re-extract, recompile and
re-test everything. This rule also checks that the re-extracted
snapshot is no newer than the current snapshot. If the
`STEEL_NIGHTLY_CI` environment variable is set to a nonempty value,
then this rule also includes the proofs from `src/proofs`, so it will
take time and memory. If you have Docker, you can run the `ci` rule
with `docker build -f src/ci/ci.Dockerfile .` which will also
install all dependencies automatically.

TODO: add GitHub Actions workflows for continuous integration
