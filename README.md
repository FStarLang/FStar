F*: An ML-like language with a type system for program verification
===================================================================

### F\* website

More information on F\* can be found at www.fstar-lang.org

### Installation

See [INSTALL.md]

[INSTALL.md]: https://github.com/FStarLang/FStar/blob/master/INSTALL.md

### Tutorial

The [F\* tutorial] provides a first taste of verified programming in F*.

[F\* tutorial]: https://www.fstar-lang.org/tutorial/

### License

This new variant of F* is released under the Apache 2.0 license;
see LICENSE for more details.

### Version 1.0

This is a new variant of F* that is still in development and we
hope will lead to a 1.0 release soon. This new variant is
incompatible and quite different compared to the previously
released 0.7 versions.

### Contacting the F* team

Please report bugs or ask questions using the GitHub issue tracker for
the FStar project:
https://github.com/FStarLang/FStar/issues
Yes, we encourage asking questions on the issue tracker!

### Editing F* code

#### Atom

The [Atom] editor has currently the best support for F*. It supports
syntax highlighting via [atom-fstar] and (Proof General style)
interactive development via [fstar-interactive].

[Atom]: https://atom.io/
[atom-fstar]: https://github.com/FStarLang/atom-fstar
[fstar-interactive]: https://github.com/FStarLang/fstar-interactive

#### Vim

[VimFStar] is a [Vim] plugin for F*.

[Vim]: http://www.vim.org/
[VimFStar]: https://github.com/FStarLang/VimFStar

#### Emacs

The [Tuareg Mode] for Objective Caml works quite well for F* too
(although some people have reported crashes).
Go for 2.0.9 (2015-03-25) or later to avoid some silly hangs that
are already fixed.
Tuareg is easiest to install using [MELPA].
To use MELPA add this to your `.emacs` or `.emacs.d/init.el` file:
```elisp
(require 'package)
(add-to-list 'package-archives
             '("melpa" . "http://melpa.milkbox.net/packages/") t)
```
Now do `M-x package-install` and install `tuareg`.

Then add the rest of the configuration to `.emacs` or `.emacs.d/init.el`:
```elisp
(add-hook 'tuareg-mode-hook 'tuareg-imenu-set-imenu)
(setq auto-mode-alist
      (append '(("\\.ml[ily]?$" . tuareg-mode)
                ("\\.topml$" . tuareg-mode))
              auto-mode-alist))
(setq auto-mode-alist 
      (append '(("\\.fs[tiy]?$" . tuareg-mode))
          auto-mode-alist))
```
Finally, if you want easy navigation through F* error messages also
add this to your `.emacs` or `.emacs.d/init.el`:
```elisp
(add-to-list 'compilation-error-regexp-alist
 '("\\([0-9a-zA-Z._/-]*.fst\\)(\\([0-9]+\\)\\,\\([0-9]+\\)-[0-9]+\\,[0-9]+)" 1 2 3))
(add-to-list 'compilation-error-regexp-alist
 '("^ERROR: Syntax error near line \\([0-9]+\\), character \\([0-9]+\\) in file \\(.*\\)$" 3 1 2))
```

[Tuareg Mode]: https://github.com/ocaml/tuareg
[MELPA]: http://melpa.org

### Executing F* code

By default F* only verifies the input code, it does not execute it.
To execute F* code one needs to translate it to OCaml
using the OCaml backend (the `--codegen OCaml` command-line argument to F*).
The generated executable OCaml code most often depends on a support library;
obtaining this support library requires
[bootstrapping in OCaml](https://github.com/FStarLang/FStar/blob/master/INSTALL.md#bootstrapping-the-compiler-in-ocaml).

The OCaml backend will produce `<ModuleName>.ml` files for each F*
module in the code.
Those `.ml` files can then be compiled into executable code using the
following command in the directory containing the ocaml files:

```
ocamlfind ocamlopt -o program -package batteries -linkpkg -thread -I $FSTAR_HOME/src/ocaml-output/ $FSTAR_HOME/src/ocaml-output/support.ml <OCamlFiles>.ml
```
where `program` is the desired name of the produced executable.
Linking the `ocaml-output` directory and `support.ml` is required if
the F* code used any built-in functions.

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

     In order to use F*, you will need to download Z3 4.3.1 or 4.3.2
     binaries and place them in this directory (or somewhere in your
     path). You can fetch these binaries from z3.codeplex.com.

     F* should also be compatible with any theorem prover that implements
     the SMT2 standard (we use no Z3-specific features). So, you 
     should be able to use another solver by passing the 
     "--smt <path to solver exe>" option to F*.
     
     
  examples/
  
     Around 22k lines of sample F* code, organized into various
     directories. All of these examples are provided as part of the
     the release so that our users have guidance on how to use the F*
     tool. 

  lib/

     Contains just two sample source files which are config files for
     the F* verifier.

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

     
