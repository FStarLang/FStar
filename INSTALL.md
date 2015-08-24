## Online editor ##

The easiest way to try out F\* is directly in your browser by using
the [online F\* editor] that's part of the [F\* tutorial].

[online F\* editor]: https://www.fstar-lang.org/run.php
[F\* tutorial]: https://www.fstar-lang.org/tutorial/

## Binary releases ##

Every now and then we release [F\* binaries on GitHub].
This is the easiest way to get F\* quickly running on your machine,
but if the release you use is old you might be missing out on new
features and bug fixes.

[F\* binaries on GitHub]: https://github.com/FStarLang/FStar/releases

## Building F* from sources ##

If you have a serious interest in F\* or want to report bugs then we
recommend that you build F\* from the sources on GitHub (the master branch).

F\* is written in a subset of F# that F\* itself can also parse with a
special flag. Therefore, the standard build process of F* is as follows:

  1. build F* from sources using the F# compiler
     (obtaining a .NET binary for F\*);
  
  2. extract the sources of F* itself to OCaml
     using the F* binary produced at step 1;
  
  3. re-build F* using the OCaml compiler from the code generated at step 2
     (obtaining a faster native binary for F\*).

**Alternative:**  If you don't care about efficiency and about the .NET
dependency you can stop already after step 1.

**Alternative:**  If you don't want to use F#/.NET/Mono at all you can
also build F\* directly from the generated OCaml sources.  Therefore, for
convenience, we keep a (possibly outdated) snapshot of the F\* sources
extracted to OCaml (the result of step 2) in the repo.  This allows
you to skip directly to step 3 and build F* with just an OCaml compiler.

### 1. Building F* from sources using the F# compiler ###

**Note:** Building F* using the recently released F# 4.0 is currently
  not supported (building suceeds but produces a broken binary:
  https://github.com/FStarLang/FStar/issues/308)

#### On Windows 7/8 using Visual Studio ####

  - Prerequisite: .NET framework 4.5

  - Prerequisite: [Visual Studio 2013 or 2015 and Visual F# Tools (v3.0 or 3.1)](http://fsharp.org/use/windows/)
    - for instance install the **free**
      [Visual Studio Community](https://www.visualstudio.com/en-us/products/visual-studio-community-vs.aspx)
    - Install the Visual F# Tools (v3.0 or 3.1) from Microsoft
      (e.g. by clicking the "Get Visual F# Tools for Visual Studio 2013"
       link [here](https://msdn.microsoft.com/en-us/vstudio/hh388569.aspx))

  - Using Visual Studio, open `FStar/VS/FStar.sln` and build the solution
    (in the menus: Build > Build Solution).

  - Get a Z3 4.3.2 binary and add it to your PATH
    - 64 bits: https://z3.codeplex.com/releases/view/135729
    - 32 bits: https://z3.codeplex.com/releases/view/135728

**Note:** on Windows you need to build F\* using Visual Studio
  (building in Cygwin is not supported currently; `make -C src`
  succeeds but produces a broken binary:
  https://github.com/FStarLang/FStar/issues/159)

**Note:** if the Visual Studio build fails because `parse.fs` and
  `lex.fs` are not found because of a mysterious issue, try closing
  and reopening the solution and rebuilding until things magically
  work (yes, we know it's strange) or do a `make -C src` for getting
  these files generated before rebuilding with Visual Studio for
  getting a proper binary:
  https://github.com/FStarLang/FStar/issues/325 and
  https://github.com/FStarLang/FStar/issues/73

#### On Linux or Mac OS X using Mono ####

  - Install mono 3.10.x or 3.12.x or 4.0.x and fsharp 3.1.x

    - On Debian/Ubuntu

            $ sudo apt-get install mono-complete fsharp

    - On Arch

            $ pacman -S mono
            $ aura -A fsharp

    - For other Linux distributions check out these links:
      - http://www.mono-project.com/download/#download-lin
      - http://fsharp.org/use/linux/

    - For Mac OS X install the MRE:
      - http://www.mono-project.com/download/#download-mac

  - Depending on your distribution, you might need to manually import
    certificates for Mono

          $ mozroots --import --sync

  - Get a Z3 4.3.2 binary and add it to your PATH

    - On Linux (any distribution, not just Ubuntu) get binary from here:
      - https://z3.codeplex.com/releases/view/101911

      For instance, for a 64bit architecture you can do

          $ wget "https://download-codeplex.sec.s-msft.com/Download/Release?ProjectName=z3&DownloadId=923684&FileTime=130586905368570000&Build=20959" -O z3-4.3.2.0713535fa6a3-x64-ubuntu-14.04.zip
          $ unzip z3-4.3.2.0713535fa6a3-x64-ubuntu-14.04.zip
          $ export PATH=z3-4.3.2.0713535fa6a3-x64-ubuntu-14.04/bin:$PATH

    - On Mac OS X get binary from here:
      - https://z3.codeplex.com/releases/view/101918

  - Compile F* from sources

          $ git clone https://github.com/FStarLang/FStar.git
          $ cd FStar
          $ make -C src

  - Try out

          $ source setenv.sh
          $ make test.net -C src

  - If `make test.net` (`make boot` in fact) causes a stack overflow try
    issuing `ulimit -s unlimited` in the terminal beforehand.


### 3. Building F* using the OCaml snapshot ###

The current version of F* requires OCaml 4.02.

#### Instructions for Windows ####

0. Install the [OCaml Installer for
   Windows](http://protz.github.io/ocaml-installer/). Make sure you ask it to
   install Cygwin -- it will just launch Cygwin's setup.exe with the right set
   of packages pre-checked, to make sure you have everything you need.

1. `make -C src/ocaml-output`

(Side note: this procedure generates a native F* binary, that is, a binary that
does *not* depend on `cygwin1.dll`, since the installer above uses a
*native* Windows port of OCaml.  Cygwin is just there to provide `make` and
other utilities required for the build.

This also means that when linking C libraries with OCaml compiled objects one
needs to use the *correct* mingw libraries and *not* the Cygwin ones. OCaml uses
special `flexlink` technology for this. See `contrib/CoreCrypto/ml` and
`examples/crypto` for examples.
)

#### Instructions for Linux and Mac OS X ####

0. Install OCaml (version 4.02.0 or later)
   - Can be installed using either your package manager or using OPAM
     (see below).

1. Install OPAM (version 1.2.x).
   - Installation instructions are available at various places
     (e.g., https://github.com/realworldocaml/book/wiki/Installation-Instructions#getting-opam
     or http://opam.ocaml.org/doc/Install.html).
     You need to initialize it by running `opam init` and update the `PATH`
     variable to the `ocamlfind` and the OCaml libraries. If you allow
     `opam init` to edit your `~/.bashrc` or `~/.profile`, it is done
     automatically; otherwise, use: `eval $(opam config env)`.

2. Install OCaml Batteries using OPAM:

        $ opam install batteries

3. Then run the following commands in `src/ocaml-output`:

        $ make


### 2. Refreshing the OCaml snapshot

0. Get an F* binary, either using the .NET build process, or the OCaml build
   process. Make sure you follow the instructions above to get a working OCaml
   setup.

1. Once you satisfy the prerequisites for your platform,
   translate the F* sources from F# to OCaml using F*.
   Run the following commands in `$FSTAR_HOME/src`:

        $ make ocaml

2. On windows, close all instances of fstar.exe, e.g. your F* IDE, because this step will overwrite fstar.exe. Then run the following commands in `src/ocaml-output`:

        $ make parser
        $ make

## Creating binary packages for your platform ##

(no cross-platform compilation supported at the moment)

0. Bootstrap the compiler in OCaml using the instructions above

1. Make sure you have the Z3 binary in your `$PATH` or
   in the `$FSTAR_HOME/bin` directory

2. Run the following command in `src/ocaml-output`:

        $ make package

3. Test that the binary is good by expanding the archive and running
   `make` in the `examples` directory inside
