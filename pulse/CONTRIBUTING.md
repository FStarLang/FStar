# Developer's guide

This section is useful only if you want to contribute to Pulse code.

In all cases (user or developer), please first read `README.md`

## Source layout

* In `src/checker`: the F* source code of the Pulse checker. This F*
  code typechecks against `lib/pulse` and `lib/pulse/core` but none of
  its other subdirectories. It does not require loading the Pulse
  plugin (which makes sense, since the checker itself is part of the
  plugin.)
* In `src/extraction`: The krml extraction rules for Pulse and
  PulseC. This F* code typechecks against the F* sources.
* In `src/syntax-extension`: A top-level parser hook for the custom
  syntax of pulse. This F* code typechecks against the F* sources.
* In `src/ocaml/plugin/generated`: A snapshot of the generated OCaml
  code for the Pulse plugin, containing the extracted implementations
  of the Pulse checker and the Pulse and PulseC extraction rules to
  krml.

## Modifying the user-facing Pulse libraries

If you want to modify the specs and proofs of the user-facing Pulse
libraries, you can work directly in `lib/pulse` and its
subdirectories. You can reverify Pulse directly with `make` from
the Pulse root directory.

Dependency diagram:

* `lib/pulse` and `lib/pulse/core` can be typechecked without loading
  the Pulse plugin
* `lib/pulse/lib` and its subdirectories depend on `lib/pulse`,
  `lib/pulse/core`, and need to load the Pulse plugin
* `lib/pulse/c` depends on `lib/pulse/lib`

## Modifying the Pulse checker

If you modify the Pulse checker in `src/checker`, you need to
regenerate and recompile the corresponding OCaml snapshot, with `make -j
boot-checker` from the Pulse root directory.

Modifying the Pulse checker does not require a source repository clone
of F*.

### Notes on the implementation of Pulse

The Pulse checker is an F* program implemented as a plugin to the F*
compiler. The sources of the core part of the plugin is in
lib/pulse in files named `Pulse.Checker.*` but also `Pulse.Typing`,
`Pulse.Soundness`. Maybe all of these should move under the
`Pulse.Checker` namespace to make it clear that they are not
user-facing.

Pulse also provides custom syntax, and this is implemented as a
OCaml/Menhir parser in `src/ocaml/plugin`, which builds an AST in
`src/syntax_extension/PulseSugar.fst`

The surface syntax parsed by the parser above is desugared to the the
Pulse AST using the code in `src/syntax_extension/PulseDesugar.fst`

Phases of the Pulse checker:

1. menhir parser produces `PulseSugar`

2. `PulseDesugar` transforms `PulseSugar` to `Pulse.Syntax.Base` (in
   `src/checker`)

3. `Pulse.Main` is the main Pulse checker, and it typechecks the
   `Pulse.Syntax.Base` AST and transforms it into `FStar.Reflection.Data`,
   the syntax of F* terms and their typing derivations.

4. The F* compiler then processes this as usual


## Modifying the Pulse or PulseC extraction rules, or the syntax extension

If you modify the Pulse or PulseC
extraction rules in `src/extraction` (`ExtractPulse.fst` and
`ExtractPulseC.fst` respectively), or the syntax extension in
`src/syntax-extension`, you need to regenerate the corresponding OCaml
snapshot.

To do so, you need to clone the F* repository and set the `FSTAR_HOME`
variable to your F* clone. Indeed, the extraction rules typecheck
against the F* sources. An opam installation of F* (or a binary
package) will not work.

Optionally, to extract C code, you must set the `KRML_HOME` environment
variable. This should point to your clone of the Karamel repository.

Then, you can extract the rules and recompile everything with `make -j
boot` from the Pulse root directory.

Alternatively, you can do `make -j full-boot`, which will remove all
generated OCaml files beforehand.

## Testing

`share/pulse` contains all examples and tests. You can run `make -j -C
share/pulse` to verify and test them. This rule will work whether you have
Karamel or not. If you have Karamel with the `KRML_HOME` variable set, then
this rule will also extract and compile (and sometimes run) C extraction
examples. Alternatively, you can run `make -j test` from the Pulse root
directory, which will build Pulse beforehand.

If you have Docker, you can run `docker build -f
src/ci/opam.Dockerfile .` to test the opam installation of Pulse
(including all dependencies.) This will also verify all examples and
tests, by moving them outside of the Pulse directory hierarchy
beforehand, to make sure that the location of those examples does not
need to depend on the location of Pulse.

Finally, you can run `make -j -C src ci` to re-extract, recompile and
re-test everything. This rule also checks that the re-extracted
snapshot is no newer than the current snapshot. If you have Docker,
you can run the `ci` rule with `docker build -f src/ci/ci.Dockerfile
.` which will also install all dependencies automatically.
