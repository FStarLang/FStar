## Table of Contents ##

  * [Online editor](#online-editor)
  * [OPAM package](#opam-package)
  * [Binary releases](#binary-releases)
    * [Testing a binary package](#testing-a-binary-package)
    * [Homebrew formula for Mac OS X](#homebrew-formula-for-mac-os-x)
    * [Chocolatey Package on Windows](#chocolatey-package-on-windows)
    * [Running F\* from a docker image](#running-f-from-a-docker-image)
  * [Building F\* from sources](#building-f-from-sources)
    * [Prerequisites: Working OCaml setup](#prerequisites-working-ocaml-setup)
      * [Instructions for Windows](#instructions-for-windows)
      * [Instructions for Linux and Mac OS X](#instructions-for-linux-and-mac-os-x)
      * [Instructions for all OSes](#instructions-for-all-oses)
    * [Step 1. Building F\* from the OCaml snapshot](#step-3-building-f-from-the-ocaml-snapshot)
    * [Step 2. Extracting the sources of F\* itself to OCaml](#step-2-extracting-the-sources-of-f-itself-to-ocaml)
  * [Runtime dependency: Z3 SMT solver](#runtime-dependency-z3-smt-solver)

## Online editor ##

The easiest way to try out F\* quickly is directly in your browser by
using either the [online F\* editor] that's part of the [F\* tutorial]
or our new [even cooler online editor] (experimental).

[online F\* editor]: https://www.fstar-lang.org/run.php
[F\* tutorial]: https://www.fstar-lang.org/tutorial
[even cooler online editor]: http://fstar.ht.vc

## OPAM package ##

If the OCaml package manager is present on your platform, you can
install the latest development version of F\* (`master` branch) and
required dependencies (except for Z3) using the following commands:

        $ opam pin add fstar --dev-repo
        $ opam install fstar

## Binary releases ##

Every now and then we release [F\* binaries on GitHub] (for Windows, Mac, and Linux)
and for Windows and Linux we also provide **experimental** [automatic weekly builds].
This is the easiest way to get F\* quickly running on your machine,
but if the build you use is old you might be missing out on new
features and bug fixes. Please do not report bugs in old releases
until making sure they still exist in the `master` branch (see
Building F\* from sources section below) or at least in the latest
[automatic weekly builds].

[F\* binaries on GitHub]: https://github.com/FStarLang/FStar/releases
[automatic weekly builds]: https://github.com/FStarLang/binaries/tree/master/weekly

### Testing a binary package ###

Test that the binary is good by expanding the archive and running the
following commands. (On Windows this requires Cygwin and `make`)

1. Add `fstar.exe` and `z3` to your `PATH`, either permanently
   or temporarily, for instance by running this:

        $ export PATH=/path/to/z3/bin:/path/to/fstar/bin:$PATH
        $ fstar.exe --version
        F* 0.9.7.0~dev
        platform=Linux_x86_64
        compiler=OCaml 4.05.0
        date=yyyy-mm-ddThh:nn:ss+02:00
        commit=xxxxxxxx
        $ z3 --version
        Z3 version 4.5.1 - 64 bit - build hashcode 1f29cebd4df6

   Note: if you are using the binary package and extracted it to,
   say, the `fstar` directory, then both `fstar.exe` and `z3` are in
   the `fstar/bin` directory.

2. Run the micro benchmarks:

        $ make -C examples/micro-benchmarks

3. If you have OCaml installed the following command should print "Hello F\*!"
   You need the same version of OCaml as was used to create the
   `fstar.exe` binary (which you can see with `fstar.exe --version`,
    as illustrated above).

        $ make -C examples/hello ocaml

   Note: to have a working OCaml install, please first read the
   [Working OCaml
   setup](#prerequisite-for-steps-2-and-3-working-ocaml-setup) section
   further below, especially steps 0 to 3 to first install OCaml on
   your OS; then use the following command to install the packages
   required to compile OCaml programs extracted from F\* code:

        $ opam install ocamlfind batteries stdint zarith ppx_deriving ppx_deriving_yojson ocaml-migrate-parsetree process

   Note: If you hand-rolled your own F* binary then remember that you need to
         also build our OCaml support library, as further documented
         [here](https://github.com/FStarLang/FStar/wiki/Executing-F*-code):

        $ make -C ulib/ml

4. You can verify the F* library and all the examples,
   keeping in mind that this might take a long time.

        $ make -j6 -C ulib examples
        $ echo $?    # non-zero means build failed! scroll up for error message!

   Note: Some of the examples require having OCaml installed (as for step 3 above).

   Note: Some of the examples require our
         [OCaml support library](https://github.com/FStarLang/FStar/wiki/Executing-F*-code)
         (as for step 3 above)

   Note: Some of the examples currently require having [KreMLin](https://github.com/FStarLang/kremlin)
         installed and the `KREMLIN_HOME` variable pointing to its location.

   Note: The option `-j6` controls the number of cores to be used in parallel build.
         Using more cores results in greater RAM usage. This can make builds slow
         if you do not have enough RAM to support all parallel builds. Consider monitoring
         RAM usage when building, and use fewer cores if you are using 100% of your RAM.

   Note: On Linux if you get a file descriptor exhaustion error that looks
         like this `Unix.Unix_error(Unix.ENOMEM, "fork", "")`
         you can increase the limits with `ulimit -n 4000`.

### Homebrew formula for Mac OS X ###

On Macs you can build and install the latest F\* release using Homebrew.
This will install F\* and all required dependencies (including Z3):

        $ brew install fstar

For building and installing the latest F\* development version from GitHub
(the `master` branch) instead of the latest release you can do:

        $ brew install --HEAD fstar

### Chocolatey Package on Windows ###

On windows you can use chocolatey package manager to install and update fstar

    > choco install fstar

or

    > cinst fstar

you can find the package description [here](https://chocolatey.org/packages/FStar)

### Running F\* from a docker image ###

An alternative to installing binaries is to install a docker image.
We currently provide the following two on docker hub: `fstarlang/fstar-emacs`
with emacs support and `fstarlang/fstar` for purists.
The image is automatically kept up to date through a cloud build.

You only have to install docker and an X server for your platform and you are good to go.
See [Running F\* from a docker image](https://github.com/FStarLang/FStar/wiki/Running-F%2A-from-a-docker-image) for the details on how to use docker.

## Building F\* from sources ##

Short version: Simply run `make -C src -j6 ocaml-fstar-ocaml` from the `master` branch of the clone.

If you have a serious interest in F\* or want to report bugs then we recommend that you build F\* from the sources on GitHub (the `master` branch).

F* is written in a subset of F* itself and can generate OCaml or F# code from its own sources.
Therefore, the standard bootstrap build process of F\* involves the following three steps:

  **Step 1.** Build F\* using the OCaml compiler from the (possibly outdated) checked-in generated OCaml code.

  **Step 2.** Extract the sources of F\* itself to OCaml using the F\* binary produced at step 1.

  **Step 3.** Repeat step 1: rebuild F\* from the newly generated OCaml code in the previous step.

Some convenience Makefile targets are available:

- To run steps 2 and 1, do `make -C src -j6 fstar-ocaml`.
- To run steps 1, 2 and 1 again (step 3), do: `make -C src -j6 ocaml-fstar-ocaml`.

**Note:** If you build F\* from sources you will also need to get a Z3 binary.
          This is further explained towards the end of this document.

### Prerequisites: Working OCaml setup  ###

The steps require a working OCaml setup. OCaml version 4.04.X, 4.05.X, 4.06.X, or 4.07.0 should work.

#### Instructions for Windows ####

1. Please use [Andreas Hauptmann's OCaml Installer for Windows](https://fdopen.github.io/opam-repository-mingw/installation/)
   to install both OCaml and OPAM.

#### Instructions for Linux and Mac OS X ####

0. Install OCaml
   - Can be installed using either your package manager or using OPAM
     (see below).

1. Install OPAM (version 1.2.x).

   - Installation instructions are available at various places
     (e.g., https://dev.realworldocaml.org/install.html
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
     range required by F\* (see above), type `opam switch ` and then
     the version number you wish to switch opam to.

4. F\* depends on a bunch of external OCaml packages which you should install using OPAM:

  ```sh
  $ opam install ocamlbuild ocamlfind batteries stdint zarith yojson fileutils pprint menhir ulex ppx_deriving ppx_deriving_yojson process pprint
  ```

  **Note:** this list of packages is longer than the list in the
  [Testing a binary package](#testing-a-binary-package) section above,
  because the additional packages here are necessary to compile F\*.

### Step 1. Building F\* from the OCaml snapshot ###

Once you have a working OCaml setup (see above)
just run the following command:

        $ make -C src/ocaml-output -j6

**Note:** On Windows this generates a native F\* binary, that is, a binary that
does *not* depend on `cygwin1.dll`, since the installer above uses a
*native* Windows port of OCaml.  Cygwin is just there to provide `make` and
other utilities required for the build.
This also means that when linking C libraries with OCaml compiled objects one
needs to use the *correct* mingw libraries and *not* the Cygwin ones. OCaml uses
special `flexlink` technology for this. See `contrib/CoreCrypto/ml` and
`examples/crypto` for examples.

### Step 2. Extracting the sources of F\* itself to OCaml ###

0. Get an F\* binary using the the OCaml build process (step 1 above).

1. Make sure you follow the instructions above to get a working OCaml setup.

2. Once you satisfy the prerequisites for your platform,
   translate the F\* sources to OCaml using F\* by running:

        $ make ocaml -C src

## Runtime dependency: Z3 SMT solver ##

To use F\* for verification you need a Z3 binary.
Our binary packages include that already in `bin`, but if you compile
F\* from sources you need to get a Z3 binary yourself and add it to
your `PATH`. We recommend you use the Everest tested binaries here:
https://github.com/FStarLang/binaries/tree/master/z3-tested
