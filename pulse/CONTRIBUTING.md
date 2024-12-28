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
* In `src/ml`: Base OCaml files for the checker.

## Modifying the user-facing Pulse libraries

If you want to modify the specs and proofs of the user-facing Pulse
libraries, you can work directly in `lib/pulse` and its
subdirectories. You can reverify Pulse directly with `make` from
the Pulse root directory.

Dependency diagram:

* `lib/common` and `lib/core` can can be typechecked without loading
  the Pulse plugin
* `lib/pulse` and its subdirectories depend on `lib/common`,
  and required the Pulse plugin
* `lib/core` and `lib/pulse` are independent as far as checking goes.
  The former is the formalization of the Pulse separation logic,
  culminating in providing the interface `Pulse.Lib.Core.fsti` in
  `lib/common`. The latter are user-facing Pulse modules.

The top-level Makefile knows about these dependencies and will parallelize
the checking.

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


### Notes on the #lang-pulse syntax extension mechanism

See F* PR https://github.com/FStarLang/FStar/pull/3363

- FStar_Parser_Parse.mly is copied into src/ocaml/plugin from the FStar repo

- src/ocaml/plugin/pulseparser.mly is an extension of FStar_Parser_Parse.mly

- In PulseASTBuilder.fst, this snippet registers `parse_extension_lang` as a parser
  for #lang-pulse blocks 

  ```
  let _ = register_extension_lang_parser "pulse" {parse_decls=parse_extension_lang}
  ```

- When the F* parser encounters a #lang-pulse, it lexes the rest of the file as
  a single token and calls `parse_extension_lang` on the contents

- `parse_extension_lang` parses the content as an interleaving of standard F*
  declarations and Pulse `fn` declarations or definitions, returning them as a
  list of FStar.Parser.AST.decl.

  - Each `fn` block is represented as an FStar.Parser.AST.DeclToBeDesugared
    containing a parsed PulseSyntaxExtension.Sugar AST

- Next, we use this to register a callback for desugaring the Sugar AST in
  PulseSyntaxExtension.ASTBuilder 
  
  ```
  let _ =
   FStar.ToSyntax.ToSyntax.register_extension_tosyntax "pulse"
   desugar_pulse_decl_callback
  ```

- `desugar_pulse_decl_callback` is invoked by F* during its desugaring phase
  with the contents of each `DeclToBeDesugared`. It is is called with the
  appropriate desugaring environment for that point in the file.

  - It returns a FStar.Syntax.Syntax.Sig_Splice, with a call into
    Pulse.Main.check_pulse_after_desugar






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

There are simple tests in `test/` and examples in `share/pulse`.
Anything that is not user-facing (like simple regression tests) should
go into `test/`. All of `share/pulse` is distributed in the package.

You can run `make -j test` to verify and test them. This rule will
work whether you have Karamel or not. If you have Karamel with the
`KRML_HOME` variable set, then this rule will also extract and compile
(and sometimes run) C extraction examples. Alternatively, you can run
`make -j test` from the Pulse root directory, which will build Pulse
beforehand.

If you have Docker, you can run `docker build -f ci/opam.Dockerfile .`
to test the opam installation of Pulse (including all dependencies.)
This will also verify all examples and tests, by moving them outside of
the Pulse directory hierarchy beforehand, to make sure that the location
of those examples does not need to depend on the location of Pulse.

Finally, you can run `make -j ci` to re-extract, recompile and re-test
everything. If you have Docker, you can run the `ci` rule with `docker
build -f ci/ci.Dockerfile .` which will also install all dependencies
automatically.
