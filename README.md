F*: An ML-like language with a type system for program verification
===================================================================

<!--
[![Build status](https://www.fstar-lang.org:3443/fstarlang/fstar/badge?branch=master)](https://www.fstar-lang.org:3443/fstarlang/fstar/)
-->

### F\* website

More information on F\* can be found at www.fstar-lang.org

### Installation

See [INSTALL.md]

[INSTALL.md]: https://github.com/FStarLang/FStar/blob/master/INSTALL.md

### Tutorial

The [F\* tutorial] provides a first taste of verified programming in F\*.

[F\* tutorial]: https://www.fstar-lang.org/tutorial/

### Version 1.0

This is a new variant of F* that is still in development and we
hope will lead to a 1.0 release soon. This new variant is
incompatible and quite different compared to the previously
released 0.7 versions.

### License

This new variant of F* is released under the Apache 2.0 license;
see `LICENSE` for more details.

### Community mailing list

The [fstar-club mailing list] is dedicated to F* users. Here is where
all F* announcements are made to the general public (e.g. for
releases, new papers, etc) and where users can ask questions, ask for
help, discuss, provide feedback, announce jobs requiring at least 10
years of F* experience, etc.

[List archives] are public, but only members can post.
[Join here][fstar-club mailing list]!

[fstar-club mailing list]: http://lists.gforge.inria.fr/mailman/listinfo/fstar-club

[List archives]: https://lists.gforge.inria.fr/pipermail/fstar-club/

### Issues

Please report issues using the [F* issue tracker] on GitHub.

[F* issue tracker]: https://github.com/FStarLang/FStar/issues

### Editing F* code

#### Atom

The [Atom] editor has currently the best support for F*. It supports
syntax highlighting via [atom-fstar] and (Proof General style)
interactive development via [fstar-interactive].

[Atom]: https://atom.io/
[atom-fstar]: https://github.com/FStarLang/atom-fstar
[fstar-interactive]: https://github.com/FStarLang/fstar-interactive

#### Vim

[VimFStar] is a [Vim] plugin for F* that also supports interactive
development and syntax highlighting.

[Vim]: http://www.vim.org/
[VimFStar]: https://github.com/FStarLang/VimFStar

#### Emacs

[fstar-mode] implements support for F* programming, including
  
  * Syntax highlighting
  * Unicode rendering (with prettify-symbols-mode)
  * Indentation
  * Real-time verification (requires the Flycheck package)
  * Interactive proofs (à la Proof-General)

 
fstar-mode requires Emacs 24.3 or newer, and is distributed through [MELPA]. Add the following to your Emacs init file (usually `.emacs`), if it is not already there:

```elisp
(require 'package)
(add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/") t)
(package-initialize)
```

Restart Emacs, and run <kbd>M-x package-refresh-contents</kbd>, then <kbd>M-x package-install RET fstar-mode RET</kbd>. Future updates can be downloaded using <kbd>M-x list-packages</kbd>.

If `fstar.exe` is not already in your path, set the `fstar-executable` variable:

```elisp
(set-default fstar-executable "PATH-TO-FSTAR.EXE")
```

[fstar-mode]: https://github.com/FStarLang/fstar-mode.el
[MELPA]: http://melpa.org

### Executing F* code

By default F* only verifies the input code, it does not compile or execute it.
To execute F* code one needs to translate it to either OCaml or F\#, using 
F\*'s code extraction facility---this is invoked using the command line
argument `--codegen OCaml` or `--codegen FSharp`.

The OCaml extractor will produce `<ModuleName>.ml` files for each F*
module in the code; whereas the F\# version will emit `<ModuleName>.fs`.

The extracted code often relies on a support library, providing, for example, 
implementations of various primitive functions provided by F\*'s standard library. 
The sources for this support library are in `lib/fs` (for F\#) and `lib/ml` (for OCaml).
To compile the code further and obtain an executable, you will need to link the
extracted code with the support library.

Several examples of how this process works can be found in the repository. 

  * `examples/hello` provides `hello.fst` and a `Makefile` that compiles and executes a hello world program in both F\# and OCaml.
  * `doc/tutorial/code/exercises` provides `ex1a-safe-read-write.fst` (a simplistic example of access control on files) and `Makefile`. The build target `acls-fs.exe` compiles and runs the code using F\#; `acls-ocaml.exe` illustrates a simple way to compile and run in OCaml; while `hard-acl` illustrates a harder, but more general way to run in OCaml.
  * `examples/crypto` provides `rpc.fst` and a `Makefile` with the `rpc-ml` target providing a way to run a small, verified example of remote procedure calls in OCaml (while linking with OpenSSL).
  * `src/ocaml-output` provides a `Makefile` which we use to [bootstrap the F\* compiler in OCaml]. 
  * `src/Makefile` provides a make target `boot-fsharp` which we use to bootstrap the F\* compiler in F\#.
  * `examples/wysteria/Makefile` contains make targets for extracting and compiling Wysteria code. Target `codegen` generates code with some admitted interfaces (`lib/ordset.fsi`, `lib/ordmap.fsi`, and `ffi.fsi`) and target `ocaml` compiles the extracted code providing concrete implementations of those interfaces.
  

### Old F* versions (v0.7.1 and earlier) ###

[F\* v0.7.1] and earlier are no longer maintained, so please do not
create any issues here about those versions.

[F\* v0.7.1]: https://github.com/FStarLang/FStar/blob/master/old/fstar-0.7.1-alpha.zip

### Code structure (partially outdated)

This section describes the general structure of the F* verifier.

#### Files

  README.md:
    This file

  INSTALL.md:
    Current installation instruction

  setenv.sh:

    A utility script that sets up the user's environment for running F*.

  LICENSE-fsharp.txt:

    The Apache 2.0 license of F# reproduced verbatim here. Most of the
    code in F* was written from scratch. However, some 1,330 lines
    of source code were derived from F#, primarily in the lexer.

#### Directories

  bin/

     Contains various binary files that the verifier uses.

     It includes binaries for the FSharp.PowerPack, various
     utilities that the verifier uses internally.

     All these binaries are available separately.

     In order to use F*, you will need to download Z3 4.4.0
     binaries and place them in your path or in this directory.
     You can fetch these binaries from z3.codeplex.com.

     F* should also be compatible with any theorem prover that implements
     the SMT2 standard (we use no Z3-specific features). So, you
     should be able to use another solver by passing the
     "--smt <path to solver exe>" option to F*.


  examples/

     Around 22k lines of sample F* code, organized into various
     directories. All of these examples are provided as part of the
     the release so that our users have guidance on how to use F*.

  lib/

     F* libraries.

  contrib/

     Additional libraries.

     Platform: Contains a Bytes.fst library used by miTLS and examples/crypto.

     CoreCrypto: Basic cryptographic algorithms as implemented by OpenSSL.


  src/

     All source code for the implementation of F* itself.

     Makefile: A top-level file for building the verifier from source
               using the command line.

     VS/FStar.sln:
        A Visual Studio (2013) solution file for all the F* sources.

     fstar.fs: The top-level file in the source tree that launches the
               verification tool.

     basic/

        A directory containing various basic utilities used throughout
        the project.

        The following files, were adapted from the Apache 2.0 release
        of F#. Each of these files quotes F#'s license at the header.

        bytes.fs (derived from fsharp/src/absil/bytes.fs)
        range.fs (derived from fsharp/src/fsharp/range.fs)


     absyn/

        A directory definition various operations over the abstract
        syntax of F* programs.


     parser/

        A directory defining a parser for F* concrete syntax into its
        abstract syntax.

        The following files, were adapted from the Apache 2.0 release
        of F#. Each of these files quotes F#'s license at the header.

        lex.fsl (derived from fsharp/src/fsharp/lex.fsl)
        lexhelp.fs (derived from fsharp/src/fsharp/lexhelp.fs)

     tc/

        The main type-checker and verification condition generator.

     tosmt/

        A module that translates F*'s logical specification into the
        SMT2 language, the input of many SMT solvers, including
        Z3. Once this translation is done, it calls into the Z3
        binaries (needs to be available in your path) to verify that
        the logical spec is valid.
