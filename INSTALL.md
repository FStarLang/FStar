## Table of Contents ##

  * [Online editor](#online-editor)
  * [Binary releases](#binary-releases)
    * [Testing a binary package](#testing-a-binary-package)
    * [OPAM package](#opam-package)
    * [Homebrew formula for Mac OS X](#homebrew-formula-for-mac-os-x)
    * [Running F* from a docker image](#running-f-from-a-docker-image)
  * [Building F* from sources](#building-f-from-sources)
    * [Step 1. Building F* from sources using the F# compiler](#step-1-building-f-from-sources-using-the-f-compiler)
      * [On Windows 7/8/10](#on-windows-7810)
      * [On Linux or Mac OS X using Mono](#on-linux-or-mac-os-x-using-mono)
    * [Prerequisite for steps 2 and 3: Working OCaml setup](#prerequisite-for-steps-2-and-3-working-ocaml-setup)
      * [Instructions for Windows](#instructions-for-windows)
      * [Instructions for Linux and Mac OS X](#instructions-for-linux-and-mac-os-x)
      * [Instructions for all OSes](#instructions-for-all-oses)
    * [Step 2. Extracting the sources of F* itself to OCaml](#step-2-extracting-the-sources-of-f-itself-to-ocaml)
    * [Step 3. Building F* from the OCaml snapshot](#step-3-building-f-from-the-ocaml-snapshot)
  * [Runtime dependency: Z3 SMT solver](#runtime-dependency-z3-smt-solver)



## Online editor ##

The easiest way to try out F\* quickly is directly in your browser by using
the [online F\* editor] that's part of the [F\* tutorial].

[online F\* editor]: https://www.fstar-lang.org/run.php
[F\* tutorial]: https://www.fstar-lang.org/tutorial/

## Binary releases ##

Every now and then we release [F\* binaries on GitHub].
This is the easiest way to get F\* quickly running on your machine,
but if the release you use is old you might be missing out on new
features and bug fixes. Please do not report bugs in old releases
until making sure they still exist in the `master` branch (see
Building F\* from sources section below).

[F\* binaries on GitHub]: https://github.com/FStarLang/FStar/releases

### Testing a binary package ###

Test that the binary is good by expanding the archive and running the
following commands. (On Windows this requires Cygwin and `make`)

1. Add `fstar.exe` and `z3` to your `PATH`, either permanently
   or temporarily, for instance by running this:

        $ export PATH=/path/to/z3/bin:/path/to/fstar/bin:$PATH
        $ fstar.exe --version
        F* 0.9.3.1-beta
        platform=Linux_x86_64
        compiler=OCaml 4.04.0
        date=2017-01-21T20:16:56+01:00
        commit=34f11c159 (dirty)
        $ z3 --version
        Z3 version 4.5.0

2. Run the unit tests:

        $ make -C examples/unit-tests

3. If you have OCaml installed run, the following command should print "Hello F*!"

        $ make -C examples/hello ocaml

4. If you have F# installed run, the following command should print "Hello F*!"

        $ make -C examples/hello fs

5. You can try verifying all the examples, but keep in mind that
   things might fail because of Z3 timeouts if your machine is not
   sufficiently powerful.

        $ make -C examples
   
   Note: Currently this is known to fail for the F# build of F\*
   ([#633](https://github.com/FStarLang/FStar/issues/633)).
   Use the OCaml build for this or stop passing `--use_hints`.

### OPAM package ###

If the OCaml package manager is present on your platform, you can
install the latest F\* release and required dependencies (except for
Z3) using the opam package:

        $ opam install fstar

Right now, the opam package is version 0.9.3-beta1. You can easily get the latest development version of F* with some opam magic:

        $ opam pin add fstar --dev-repo

### Homebrew formula for Mac OS X ###

On Macs you can also build and install the latest F\* release using Homebrew.
This will install F\* and all required dependencies (including Z3):

        $ brew install fstar

For building and installing the latest F\* sources from GitHub (the `master` branch)
instead of the latest release you can do:

        $ brew install --HEAD fstar

### Running F* from a docker image ###

An alternative to installing binaries is to install a docker image.
We currently provide the following two on docker hub: `fstarlang/fstar-emacs`
with emacs support and `fstarlang/fstar` for purists.
The image is automatically kept up to date through a cloud build.

You only have to install docker and an X server for your platform and you are good to go.
See [Running F* from a docker image] (https://github.com/FStarLang/FStar/wiki/Running-F%2A-from-a-docker-image) for the details on how to use docker.



## Building F* from sources ##

If you have a serious interest in F\* or want to report bugs then we
recommend that you build F\* from the sources on GitHub (the `master` branch).

F\* is written in a subset of F# that F\* itself can also parse with a
special flag. Therefore, the standard build process of F* involves the following
three steps:

  **Step 1.** build F* from sources using the F# compiler
     (obtaining a .NET binary for F\*);

  **Step 2.** extract the sources of F* itself to OCaml
     using the F* binary produced at step 1 (or even a previous step 3);

  **Step 3.** re-build F* using the OCaml compiler from the code
     generated at step 2 (obtaining a faster native binary for F\*).

**Note:** If you build F* from sources you will also need to get a Z3
binary. This is further explained towards the end of this document.

**Easier alternative:**  If you don't care about efficiency, about the .NET
dependency and quite a few bugs ([#746](https://github.com/FStarLang/FStar/issues/746))
you can stop already after step 1.

**Easier alternative:**  If you don't want to use F#/.NET/Mono at all you can
also build F\* directly from the generated OCaml sources.  Therefore, for
convenience, we keep a (possibly a bit outdated) snapshot of the F\* sources
extracted to OCaml (the result of step 2) in the repo.  This allows
you to skip directly to step 3 and build F* with just an OCaml compiler.

Some convenience Makefile targets are available for steps 2 and 3:

- To run steps 2 and 3, do `make -j 15 fstar-ocaml`.
- To run steps 3, 2 and 3 again, do: `make -j 15 ocaml-fstar-ocaml`.

The latter step is not always guaranteed to work but almost always does,
and is a tiny bit faster than extracting F* using the F# version.


### Step 1. Building F* from sources using the F# compiler ###

#### On Windows 7/8/10 ####

  - Prerequisite: .NET framework 4.5

  - Prerequisite: [Visual Studio 2015 and Visual F# Tools](http://fsharp.org/use/windows/)
    - for instance install the **free**
      [Visual Studio Community](https://www.visualstudio.com/en-us/products/visual-studio-community-vs.aspx)
    - The Visual F# Tools are installed automatically when you first
      create or open an F# project.

**Easy alternative:** open a Cygwin command prompt, and run `make`
from the `src` directory. This will run `msbuild` on the Visual Studio
solution file; in effect, this performs exactly what you would get by
clicking the "Build" button within Visual Studio.

Read on for the more complete solution involving Visual Studio itself.

  - Run the `src/VS/nuget-restore.bat` script _from the top-level F* directory_
    before opening the solution for the first time.
    F* depends upon NuGet packages that are incompatible with
    Visual Studio's internal invocation of NuGet's restore feature.

        C:\Users\xxx\Desktop\FStar>src\VS\nuget-restore.bat
        Installing 'FsLexYacc.Runtime 6.1.0'.
        Installing 'FsLexYacc 6.1.0'.
        Successfully installed 'FsLexYacc.Runtime 6.1.0'.
        Successfully installed 'FsLexYacc 6.1.0'.
        All packages listed in packages.config are already installed.

  - Using Visual Studio, open `src/VS/FStar.sln` and build the solution
    (in the menus: Build > Build Solution). **Make sure to choose the 'Release' configuration**.
    Note: the 'Debug' configuration may be the default, although it has no optimizations enabled
    and is not capable of bootstrapping.

**Note:** If Visual Studio fails to open one or more projects, the
  problem is likely that the NuGet package cache hasn't been
  restored. You must either exit Visual Studio to restore the cache
  (using the `src/VS/nuget-restore.bat` script), or restart Visual
  Studio after having restored the cache. Otherwise, F* may not
  successfully build (or correctly build).

#### On Linux or Mac OS X using Mono ####

  - Install mono (any version from 4.0.3.0 to 4.6.x.y) and fsharp (version 4.0.1.x)

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
    certificates for Mono (you don't need to do this on Arch if you
    use the default `mono` package)

          $ mozroots --import --sync

  - Compile F* from sources

          $ git clone https://github.com/FStarLang/FStar.git
          $ cd FStar
          $ make -C src

  - Try out binary using [the instructions above](https://github.com/FStarLang/FStar/blob/master/INSTALL.md#testing-a-binary-package).
  
  - Another thing you can try is bootstrapping the F\* compiler:

          $ export PATH=/path/to/fstar/bin:$PATH
          $ make -C src boot

    If `make boot` causes a stack overflow try issuing `ulimit -s unlimited` in the terminal beforehand.

Note: you may want to make the `PATH` change permanent by adding:

```
export PATH=/path/to/fstar/bin:$PATH
```

into your `~/.bashrc`.

### Prerequisite for steps 2 and 3: Working OCaml setup  ###

Steps 2 and 3 below require a working OCaml (any version from 4.02.2 to 4.04.0) setup.

#### Instructions for Windows ####

Please use the  [OCaml Installer for Windows](http://protz.github.io/ocaml-installer/).
Follow the [installation guide](https://github.com/protz/ocaml-installer/wiki)
that's over there (it's optimized for F*). This will install both OCaml and OPAM.

#### Instructions for Linux and Mac OS X ####

0. Install OCaml (any version from 4.02.2 to 4.03.0)
   - Can be installed using either your package manager or using OPAM
     (see below).

1. Install OPAM (version 1.2.x).

   - Installation instructions are available at various places
     (e.g., https://github.com/realworldocaml/book/wiki/Installation-Instructions#getting-opam
     or http://opam.ocaml.org/doc/Install.html).

#### Instructions for all OSes ####

2. Initialize and configure OPAM

   - You need to initialize it by running `opam init` and update the `PATH`
     variable to the `ocamlfind` and the OCaml libraries. If you allow
     `opam init` to edit your `~/.bashrc` or `~/.profile`, it is done
     automatically; otherwise, use: `eval $(opam config env)`.

   - If you're on Windows see https://github.com/protz/ocaml-installer/wiki
     for instructions on how to configure your environment for use with OPAM

3. Ensure that OPAM is using a recent enough version of OCaml

   - Type `opam switch list`. The current OCaml version used by opam
     is identified by the letter C. If it is not within the version
     range required by F* (see above), type `opam switch ` and then
     the version number you wish to switch opam to.

4. F* depends on a bunch of external OCaml packages which you should install using OPAM:

  ```sh
  $ opam install ocamlbuild ocamlfind batteries stdint zarith yojson fileutils pprint
  ```
  Some of the examples also require the `sqlite3` opam package, which depends
  on SQLite itself that you can install with `opam depext sqlite3` (at least on Linux)

### Step 2. Extracting the sources of F* itself to OCaml ###

0. Get an F* binary, either using the F#/.NET build process (step 1
   above; remember to build a Release version, else you'll get a
   `StackOverflowException` in `make ocaml -C src` below),
   or the OCaml build process (step 3 above).

1. Make sure you follow the instructions above to get a working OCaml setup.

2. Once you satisfy the prerequisites for your platform,
   translate the F* sources from F# to OCaml using F* by running:

        $ make ocaml -C src

### Step 3. Building F* from the OCaml snapshot ###

Once you have a working OCaml setup (see above)
just run the following command:

        $ make -C src/ocaml-output -j 15

The option `-j 15` controls the number of cores to be used in parallel build. This is a relatively standard unix feature.

**Note:** On Windows this generates a native F* binary, that is, a binary that
does *not* depend on `cygwin1.dll`, since the installer above uses a
*native* Windows port of OCaml.  Cygwin is just there to provide `make` and
other utilities required for the build.
This also means that when linking C libraries with OCaml compiled objects one
needs to use the *correct* mingw libraries and *not* the Cygwin ones. OCaml uses
special `flexlink` technology for this. See `contrib/CoreCrypto/ml` and
`examples/crypto` for examples.

## Runtime dependency: Z3 SMT solver ##

To use F* for verification you need a Z3 4.5.0 binary.
Our binary packages include that already in `bin`, but if you compile
F* from sources you need to get a Z3 binary yourself and add it to
your `PATH`. We recommend you use the 4.5.0 binaries here:
https://github.com/Z3Prover/z3/releases/tag/z3-4.5.0
