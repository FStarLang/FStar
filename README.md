FStar
=====

An ML-like language with a type system for program verification

--------------------------------------------------------------------------------
 
This note describes the general structure of the F* verifier and its code.

Files:

  README.txt: 
    This file

  setenv.sh: 

    A utility script that sets up the user's environment for running F*.

  LICENSE-fsharp.txt:  

    The Apache 2.0 license of F# reproduced verbatim here. Most of the 
    code in F* was written from scratch. However, some 1,330 lines
    of source code were derived from F#, primarily in the lexer.

Directories:

  bin/

     Contains various binary files that the verifier uses. 

     It includes binaries for the FSharp.PowerPack, various
     utilities that the verifier uses internally. 

     All these binaries are available separately. 

     In order to use F*, you will need to separately download Z3
     binaries and place them in this directory. You can fetch these
     binaries from z3.codeplex.com.
     
     
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
        A Visual Studio (2012) solution file for all the F* sources.

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

     
