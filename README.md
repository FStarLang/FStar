FStar
=====

An ML-like language with a type system for program verification


-----------------------------------

This note describes the general structure of the F* verifier and its code.

Files:

  README.txt: 
    This file

  setenv.sh: 

    A utility script that sets up the user's environment for running F*.

  LICENSE-fsharp.txt:  

    The Apache 2.0 license of F# reproduced verbatim here. Of the
    ~20,000 lines of source code included here, a total of 1,330 lines
    of source code was derived from F#. The rest was written from
    scratch, primarily by N. Swamy. This is documented in further
    detail below.

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
     
     fstar.fsproj: A project file for building the verifier using
                   Visual Studio.
     

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

     tccore/
     
        Various utilities to operate over F* types and type environments.


     monadic/
     
        The main verification condition generator for F*. This is the
        module that derives a logical specification for an F* program. 


     z3encode/
     
        A module that translates F*'s logical specification into the
        input language of Z3. Once this translation is done, it calls
        into the Z3 binaries (provided in /bin) to verify that the
        logical spec is valid.

     
