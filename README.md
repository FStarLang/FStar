F*: An ML-like language with a type system for program verification
===================================================================


### Version 1.0

This is a new variant of F* that is still in development and we
hope will lead to a 1.0 release soon. This new variant is
incompatible and quite different compared to the previously
released 0.7 versions. 

### Installation

See [INSTALL.md]

[INSTALL.md]: https://github.com/FStarLang/FStar/blob/master/INSTALL.md

### Tutorial

The [F\* tutorial] provides a first taste of verified programming in F*.

[F\* tutorial]: http://prosecco.gforge.inria.fr/tutorial.html

### License

This new variant of F* is released under the Apache 2.0 license;
see LICENSE for more details.

### Code structure

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

     
