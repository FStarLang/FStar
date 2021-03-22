## Table of Contents ##

  * [Online editor](#online-editor)
  * [OPAM package](#opam-package)
  * [Binary package](#binary-package)
    * [Testing a binary package](#testing-a-binary-package)
  * [Running F* from a docker image](#running-f-from-a-docker-image)
  * [Chocolatey Package on Windows](#chocolatey-package-on-windows)
  * [Building F* from the OCaml sources](#building-f-from-the-ocaml-sources)
    * [Prerequisites: Working OCaml setup](#prerequisites-working-ocaml-setup)
      * [Instructions for Windows](#instructions-for-windows)
      * [Instructions for Linux and Mac OS X](#instructions-for-linux-and-mac-os-x)
      * [Instructions for all OSes](#instructions-for-all-oses)
    * [Step 1. Building F* from the OCaml snapshot](#step-1-building-f-from-the-ocaml-snapshot)
    * [Step 2l. Building the F* libraries](#step-2l-building-the-f-libraries)
  * [Bootstrapping F* in OCaml](#bootstrapping-f-in-ocaml)
    * [Step 1. Build an F* binary from OCaml snapshot](#step-1-build-an-f-binary-from-ocaml-snapshot)
    * [Step 2b. Extract the sources of F* itself to OCaml](#step-2b-extract-the-sources-of-f-itself-to-ocaml)
    * [Repeat Step 1](#repeat-step-1)
  * [Runtime dependency: Particular version of Z3](#runtime-dependency-particular-version-of-z3)

## Online editor ##

The easiest way to try out F\* quickly is directly in your browser by
using the [online F\* editor] that's part of the [F\* tutorial].

[online F\* editor]: https://www.fstar-lang.org/run.php
[F\* tutorial]: https://www.fstar-lang.org/tutorial

## OPAM package ##

If the OCaml package manager (OPAM version 2.0 or later) is present on your platform,
you can install the latest development version of F\* (`master` branch) and
required dependencies ([except for Z3](#runtime-dependency-particular-version-of-z3))
using the following command:

    $ opam pin add fstar --dev-repo

To instead install the latest released version you can use the following command
(keeping in mind that you will often get an old version of F\* this way,
so unless a release happened recently we don't really recommend it):

    $ opam install fstar

Note: To install OCaml and OPAM on your platform please read the
[Working OCaml setup](#prerequisites-working-ocaml-setup)
section further below, steps 0 to 3.

Note: On MacOS you will additionally need to install `coreutils`
via Homebrew or Macports for the OPAM package of F\* to work
(see [issue #469](https://github.com/FStarLang/FStar/issues/469)).

## Binary package ##

Every year or so we release [F\* binaries on GitHub] (for Windows, Mac, and Linux)
and for Windows and Linux we also try to provide [automatic weekly builds].
This is a way to get F\* quickly running on your machine,
but if the build you use is old you might be missing out on new
features and bug fixes. Please do not report bugs in old releases
until making sure they still exist in the `master` branch (see
[OPAM package](#opam-package) above and
[Building F\* from sources](#building-f-from-the-ocaml-sources) below)
or in one of the recent [automatic weekly builds].

[F\* binaries on GitHub]: https://github.com/FStarLang/FStar/releases
[automatic weekly builds]: https://github.com/FStarLang/binaries/tree/master/weekly

### Testing a binary package ###

You can test that the binary is good if you wish, by expanding the archive and
running the following commands. (Note: On Windows this requires Cygwin and `make`)

1. Add `fstar.exe` and `z3` to your `PATH`, either permanently
   or temporarily, for instance by running this:

        $ export PATH=/path/to/fstar/bin:$PATH
        $ fstar.exe --version
        F* 0.9.7.0-alpha1
        platform=Linux_x86_64
        compiler=OCaml 4.12.0
        date=yyyy-mm-ddThh:nn:ss+02:00
        commit=xxxxxxxx
        $ z3 --version
        Z3 version 4.8.5 - 64 bit

   Note: if you are using the binary package and extracted it to, say, the
   `/path/to/fstar` directory, then both `fstar.exe` and the right version of
   `z3` are in the `path/to/fstar/bin` directory.

2. Run the micro benchmarks:

        $ make -C tests/micro-benchmarks

3. Verify the F\* standard library, producing `.checked` files that cache
   definitions to speed up subsequent usage:

        $ make -C ulib -j6
        $ echo $?    # non-zero means build failed! scroll up for error message!

   Note: The option `-j6` controls the number of cores to be used in parallel build.
         Using more cores results in greater RAM usage. This can make builds slow
         if you do not have enough RAM to support all parallel builds. Consider monitoring
         RAM usage when building, and use fewer cores if you are using 100% of your RAM.

4. If you have a working OCaml setup and intend to extract and compile OCaml code
   against our OCaml support library, please build it first with:

        $ make -C ulib install-fstarlib

   Then the following command should print "Hello F\*!"

        $ make -C examples/hello hello

   For more on extracting to OCaml, check out
   [the documentation on extracting and executing F\* code](https://github.com/FStarLang/FStar/wiki/Executing-F*-code).

   Note: If you still need to obtain a working OCaml setup, please read
   [the corresponding section below](#prerequisites-working-ocaml-setup),
   especially steps 0 to 3 to first install OCaml and OPAM on
   your OS; then use the following command to install the packages
   required to compile OCaml programs extracted from F\* code:

        $ opam install ocamlfind batteries stdint zarith yojson ppx_deriving ppx_deriving_yojson ppxlib=0.22.0 process

5. (Optional) You can also verify all the examples, keep in mind that this will
   take a long time, use a lot of resources, and there are also some quirks
   explained in the notes below.

        $ make -C examples -j6
        $ echo $?    # non-zero means build failed! scroll up for error message!

   Note: As for step 4 above some of the examples require having OCaml installed
         and some additionally our [OCaml support library](https://github.com/FStarLang/FStar/wiki/Executing-F*-code).

   Note: Some of the examples currently require having [KreMLin](https://github.com/FStarLang/kremlin)
         installed and the `KREMLIN_HOME` variable pointing to its location.

   Note: On Linux if you get a file descriptor exhaustion error that looks
         like this `Unix.Unix_error(Unix.ENOMEM, "fork", "")`
         you can increase the limits with `ulimit -n 4000`.

## Running F\* from a docker image ##

An alternative to installing binaries is to install a docker image.
We currently provide the following two on docker hub: `fstarlang/fstar-emacs`
with emacs support and `fstarlang/fstar` for purists.
The image is automatically kept up to date through a cloud build.

You only have to install docker and an X server for your platform and you are good to go.
See [Running F\* from a docker image](https://github.com/FStarLang/FStar/wiki/Running-F%2A-from-a-docker-image)
for the details on how to use docker.

## Chocolatey Package on Windows ##

On windows you can use chocolatey package manager to install and update the
latest released version of F\*. (Keep in mind that you will often get an old
version of F\* this way, so unless a release happened recently we don't really
recommend it.)

    > choco install fstar

or

    > cinst fstar

you can find the package description [here](https://chocolatey.org/packages/FStar)

## Building F\* from the OCaml sources ##

If you have a serious interest in F\* then we recommend that you build
F\* from the sources on GitHub (the `master` branch).

**Short version**:
Once you have a [working OCaml setup](#prerequisites-working-ocaml-setup),
simply run `make -j 6` from the `master` branch of the clone.
This build process is explained in smaller steps [below](#step-1-building-f-from-the-ocaml-snapshot),
but first we explain how to get a working OCaml setup on your machine.

**Note:** To use F\* you will also need to [get a particular version of Z3](#runtime-dependency-particular-version-of-z3).

### Prerequisites: Working OCaml setup  ###

The steps require a working OCaml setup. OCaml version from 4.04.0 to 4.12.X should work.

#### Instructions for Windows ####

1. Please use [Andreas Hauptmann's OCaml Installer for Windows](https://fdopen.github.io/opam-repository-mingw/installation/)
   to install both OCaml and OPAM.

2. If needed switch to a supported OCaml version by running the following commands:
  ```sh
  $ opam update
  $ opam switch list-available
  $ opam switch create ocaml-variants.4.12.0+mingw64c
  ```

3. Afterwards you can install the `depext` and `depext-cygwinports` packages,
  to be able to install some binary dependencies below more easily.
  ([More documentation on depext-cygwin here](https://fdopen.github.io/opam-repository-mingw/depext-cygwin/).)
  ```sh
  $ opam install depext depext-cygwinports
  ```

Then follow step 4 in [Instructions for all OSes](#instructions-for-all-oses) below.

#### Instructions for Linux and Mac OS X ####

0. Install OCaml
   - Can be installed using either your package manager or using OPAM
     (see below).

1. Install OPAM (version 2.0 or later).

   - Installation instructions are available at
     [various](http://opam.ocaml.org/doc/Install.html)
     [places](https://dev.realworldocaml.org/install.html).

2. Initialize and configure OPAM

   - You need to initialize it by running `opam init` and update the `PATH`
     variable to the `ocamlfind` and the OCaml libraries. If you allow
     `opam init` to edit your `~/.bashrc` or `~/.profile`, it is done
     automatically; otherwise, use: `eval $(opam config env)`.

3. Ensure that OPAM is using a supported version of OCaml

   - Type `opam switch list`. The current OCaml version used by opam
     is identified by the letter C. If it is not within the version
     range required by F\* ([see above](#prerequisites-working-ocaml-setup)),
     type `opam switch list-available`
     to see what versions are available and then `opam switch <version-number>`.

   - Afterwards you can also install the `depext` package,
     to be able to install some binary dependencies below more easily.
     ```sh
     $ opam install depext
     ```

  Then follow [step 4](#instructions-for-all-oses) below.

#### Instructions for all OSes ####

4. F\* depends on a bunch of external OCaml packages which you should install using OPAM:

  ```sh
  $ opam install ocamlbuild ocamlfind batteries stdint zarith yojson fileutils pprint menhir sedlex ppx_deriving ppx_deriving_yojson process ppxlib=0.22.0
  ```

  **Note:** This list of opam packages is longer than the list in the
  [Testing a binary package](#testing-a-binary-package) section above,
  because the additional packages here are necessary to compile F\*.

  **Note:** Some of these opam packages depend on binary packages that you need to install locally
  (eg, using your Linux package manager). So if the command above gives you errors like this:
  ```sh
  [ERROR] The compilation of conf-gmp failed at "./test-win.sh".
  ```
  You can use `depext` to install the missing binary packages, for instance:
  ```sh
  $ opam depext -i conf-gmp
  ```
  On Windows, for dynamic libraries like gmp, you should add `/usr/x86_64-w64-mingw32/sys-root/mingw/bin:/usr/i686-w64-mingw32/sys-root/mingw/bin` to your cygwin `$PATH`.
  If you additionally want to call `bin/fstar.exe` from Windows or VSCode (not just from a cygwin shell),
  you also need to add the corresponding Windows paths (like `C:\OCaml32\usr\i686-w64-mingw32\sys-root\mingw\bin`) to your
  Windows `$PATH`. Otherwise you will get popups like this when trying to call fstar.exe outside cygwin:
  ```sh
  The code execution cannot proceed because libgmp-10.dll was not found. Reinstall the program may fix this problem.
  ```

### Step 1. Building F\* from the OCaml snapshot ###

Once you have a working OCaml setup (see above) just run the following command:

    $ make 1 -j6

As explained in more detail [below](#bootstrapping-f-in-ocaml), a snapshot of
the F\* sources extracted to OCaml is checked in the F\* repo and regularly
updated, and the command above will simply build an F\* binary out of that snapshot.

**Note:** On Windows this generates a *native* F\* binary, that is, a binary
that does *not* depend on `cygwin1.dll`, since
[the installer above](#instructions-for-windows) uses a
*native* Windows port of OCaml.  Cygwin is just there to provide `make` and
other utilities required for the build.
This also means that when linking C libraries with OCaml compiled objects one
needs to use the *correct* mingw libraries and *not* the Cygwin ones. OCaml uses
special `flexlink` technology for this. See `examples/crypto` and
`contrib/CoreCrypto/ml` for examples.

### Step 2l. Building the F\* libraries ###

Just run:

    $ make -C ulib/ -j6

It does two things:

1. It verifies the F\* standard library, producing `.checked` files that cache
   definitions to speed up subsequent usage.

2. It builds the various OCaml libraries (`fstar-compiler-lib`, `fstarlib`,
   `fstartaclib`), needed for building OCaml code extracted from F\*, native
   tactics, etc. You can build this part separately with:

        $ make libs

   (this target will also rebuild `fstar.exe`, since these libraries tightly
   depend on the executable). This rule does NOT verify anything.

## Bootstrapping F\* in OCaml

F\* is written in a subset of F\* itself and can generate OCaml code from its own sources.
Therefore, the standard bootstrap build process of F\* involves the following three steps:

  **Step 1.** Build F\* using the OCaml compiler from the (possibly outdated) checked-in generated OCaml snapshot.

  **Step 2b.** Extract the sources of F\* itself to OCaml using the F\* binary produced at step 1.

  **Repeat step 1**: Rebuild F\* from the newly generated OCaml code in the previous step.

A convenience Makefile target is available to run all three steps:

    $ make boot -j6

### Step 1. Build an F\* binary from OCaml snapshot ###

[Get an F\* binary using the the OCaml build process](#step-1-building-f-from-the-ocaml-snapshot):

    $ make 1 -j6

### Step 2b. Extract the sources of F\* itself to OCaml ###

1. Make sure you follow the instructions above to get a
   [working OCaml setup](#prerequisites-working-ocaml-setup).

2. Once you satisfy the prerequisites for your platform,
   translate the F\* sources to OCaml using F\* by running:

        $ make ocaml -C src -j6

### Repeat [Step 1](#step-1-build-an-f-binary-from-ocaml-snapshot)

## Runtime dependency: Particular version of Z3 ##

To use F\* for verification you need a particular Z3 binary.
Our binary packages include that already in `bin`, but if you compile
F\* from sources you need to get the Z3 binary yourself and add it to
your `PATH`. We strongly recommend to use the corresponding binary here:
https://github.com/FStarLang/binaries/tree/master/z3-tested

Other versions of Z3 may well work, but the F* tests, standard library, and
examples take a strong dependency on the particular Z3 binary above.
They will likely fail to verify with any other Z3 version.
