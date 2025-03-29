## Table of Contents ##

  * [Online editor](#online-editor)
  * [OPAM package](#opam-package)
  * [Binary package](#binary-package)
    * [Installing a binary package](#installing-a-binary-package)
    * [Testing a binary package](#testing-a-binary-package)
  * [Running F* from a docker image](#running-f-from-a-docker-image)
  * [Chocolatey Package on Windows](#chocolatey-package-on-windows)
  * [Nix Package](#nix-package)
  * [Building F* from the OCaml sources](#building-f-from-the-ocaml-sources)
    * [Prerequisites: Working OCaml setup](#prerequisites-working-ocaml-setup)
      * [Instructions for Windows](#instructions-for-windows)
      * [Instructions for Linux and Mac OS X](#instructions-for-linux-and-mac-os-x)
      * [Instructions for all OSes](#instructions-for-all-oses)
    * [Building F* and the libraries](#building-f-and-its-libraries)
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

## Runtime dependency: Particular version of Z3 ##

F\* requires specific versions of Z3 to work correctly,
and will refuse to run if the version string does not match.
You should have `z3-4.8.5` and `z3-4.13.3` in your `$PATH`:

```
❯ z3-4.8.5 --version
Z3 version 4.8.5 - 64 bit

❯ z3-4.13.3 --version
Z3 version 4.13.3 - 64 bit
```

On Linux you can install these two versions with the following command:
```bash
sudo .scripts/get_fstar_z3.sh /usr/local/bin
```

## OPAM package ##

If the OCaml package manager (OPAM version 2.0 or later) is present on your platform,
you can install the latest released version of F* and required dependencies
using the following command:

    $ opam install fstar

To instead install the latest development version (`master` branch) you can
use the following command:

    $ opam pin add fstar --dev-repo

Note: To install OCaml and OPAM on your platform please read the
[Working OCaml setup](#prerequisites-working-ocaml-setup)
section further below, steps 0 to 3.


## Binary package ##

Every week or so we release [F\* binaries on GitHub] (for Windows and Linux).
This is a way to get F\* quickly running on your machine,
but if the build you use is old you might be missing out on new
features and bug fixes. Please do not report bugs in old releases
until making sure they still exist in the `master` branch (see
[OPAM package](#opam-package) above and
[Building F\* from sources](#building-f-from-the-ocaml-sources) below).

[F\* binaries on GitHub]: https://github.com/FStarLang/FStar/releases

Using a binary package allows you to use F* even if you do not want to
install OCaml on your machine. You will be able to verify F* code, and
to generate OCaml code from F*; but if you want to compile such
generated OCaml code, then you will need OCaml.

### Installing a binary package ###

After downloading a binary package and extracting its contents, you
need to perform the following step before your first use:

   Add `fstar.exe` and `z3` to your `PATH`, either permanently
   or temporarily, for instance by running this:

        $ export PATH=/path/to/fstar/bin:$PATH
        $ fstar.exe --version
        F* 0.9.8.0~dev
        platform=Linux_x86_64
        compiler=OCaml 4.14.0
        date=yyyy-mm-ddThh:nn:ss+02:00
        commit=xxxxxxxx
        $ z3-4.13.3 --version
        Z3 version 4.13.3 - 64 bit

   Note: if you are using the binary package and extracted it to, say, the
   `/path/to/fstar` directory, then both `fstar.exe` and the right version of
   `z3` are in the `path/to/fstar/bin` directory.

### Testing a binary package ###

After installing a F* binary package as described above, you can test
that the binary is good if you wish, by running the following
commands. (Note: On Windows this requires Cygwin and `make`)

1. You can run the micro benchmarks:

        $ make -C tests/micro-benchmarks


2. You can also verify all the examples, keep in mind that this will
   take a long time, use a lot of resources, and there are also some quirks
   explained in the notes below.

        $ make -C examples -j6 HAS_OCAML=
        $ echo $?    # non-zero means build failed! scroll up for error message!

   Note: Some of the examples need to generate and compile OCaml
         code. The `HAS_OCAML=` argument to `make` disables those
         parts of those examples that rely on OCaml. If, however, you
         remove that option, then you will most likely encounter
         version discrepancies between the OCaml support libraries
         included in the F\* binary packages and the OCaml libraries
         and packages installed on your system. This is why, to avoid
         such discrepancies, you should install F\* via opam if you
         are interested in compiling these examples.

   Note: Some of the examples currently require having [KaRaMeL](https://github.com/FStarLang/karamel)
         installed and the `KRML_HOME` variable pointing to its location.
         If KaRaMeL is absent, then these examples will be skipped.

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

## Nix Package ##

On [Linux](https://nixos.org/download.html#nix-install-linux),
[MacOS](https://nixos.org/download.html#nix-install-macos) or
[Windows](https://nixos.org/download.html#nix-install-windows) (using
WSL2), you can use the [Nix package manager](https://nixos.org/) to
install F* from sources in a reproducible way, possibly with binaries
cached.

**Bleeding-edge F\* from sources:**

Install Nix and F\* `master` in one go with two lines of bash:
```bash
# 1. Install the Nix package manager manager (as https://nixos.org/download.html)
sh <(curl -L https://nixos.org/nix/install) --daemon
# 2. Build and install F\* in your profile environment
nix profile install github:FStarLang/FStar --experimental-features 'nix-command flakes'
```

For more information about building F\* from sources with Nix, see
[`./.nix/README.md`](./.nix/README.md).

**F\* release with binary cache**:

If you don't need bleeding-edge F\*, the Nix package collection
[Nixpkgs](https://github.com/NixOS/nixpkgs) provides F\* builds with
binary cache. The command `nix-shell -p fstar` will drop you in a bash
shell with F\*'s binary availaible in path.


## Building F\* from the OCaml sources ##

If you have a serious interest in F\* then we recommend that you build
F\* from the sources on GitHub (the `master` branch).

**Short version**:
Once you have a [working OCaml setup](#prerequisites-working-ocaml-setup),
simply run `make -j 6` from the `master` branch of the clone.
First we explain how to get a working OCaml setup on your machine.

**Note:** To compile and use F\* from its sources, you will also need
  to [get a particular version of
  Z3](#runtime-dependency-particular-version-of-z3).

### Prerequisites: Working OCaml setup  ###

The steps require a working OCaml setup. OCaml version 4.14.X should work.

#### Instructions for Windows ####

1. Please use [Andreas Hauptmann's OCaml Installer for Windows](https://fdopen.github.io/opam-repository-mingw/installation/)
   to install both OCaml and OPAM.

2. If needed switch to a supported OCaml version by running the following commands:
  ```sh
  $ opam update
  $ opam switch list-available
  $ opam switch create ocaml-variants.4.14.0+mingw64c
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

   - Afterwards you can also install the `depext` package if you are on OPAM version lower then 2.1,
     to be able to install some binary dependencies below more easily. Version of OPAM after 2.1 has depext handling baked in.
     ```sh
     $ opam install depext
     ```

  Then follow [step 4](#instructions-for-all-oses) below.

#### Instructions for all OSes ####

4. F\* depends on a bunch of external OCaml packages which you should install using OPAM:

  ```sh
  $ opam install --deps-only .
  ```

  **Note:** On some Linux distributions, for example Gentoo, where `opambuild` comes pre-installed, you may need run
  `CHECK_IF_PREINSTALLED=false opam install .` instead to prevent build failures.

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
  you also need to add the corresponding Windows paths (like `C:\cygwin64\usr\i686-w64-mingw32\sys-root\mingw\bin`) to your
  Windows `$PATH`. Otherwise you will get popups like this when trying to call fstar.exe outside cygwin:
  ```sh
  The code execution cannot proceed because libgmp-10.dll was not found. Reinstall the program may fix this problem.
  ```

### Building F\* and its libraries ###

Once you have a working OCaml setup (see above) just run the following
command (you can use -j N, where N is a parallel factor suitable for
your machine):

    $ make -j N

This does two things:

1. As explained in more detail [below](#bootstrapping-f-in-ocaml), a snapshot of
   the F\* sources extracted to OCaml is checked in the F\* repo and regularly
   updated, and the command above will simply build an F\* binary out of that snapshot.

   That snapshot also contains the extracted OCaml code of the various
   OCaml libraries needed for building OCaml code extracted from F\*,
   native tactics, etc., so this step also compiles them.

   This step can be isolatedly run with `make dune-fstar`

   **Note:** On Windows this generates a *native* F\* binary, that is,
   a binary that does *not* depend on `cygwin1.dll`, since [the installer above](#instructions-for-windows)
   uses a *native* Windows
   port of OCaml.  Cygwin is just there to provide `make` and other
   utilities required for the build.  This also means that when
   linking C libraries with OCaml compiled objects one needs to use
   the *correct* mingw libraries and *not* the Cygwin ones. OCaml uses
   special `flexlink` technology for this. See `examples/crypto` and
   `contrib/CoreCrypto/ml` for examples.

2. The command above verifies the F\* standard library, producing
   `.checked` files that cache definitions to speed up subsequent
   usage.

   This step can be isolatedly run with `make verify-ulib`

## Bootstrapping F\* in OCaml

F\* is written in a subset of F\* itself and can generate OCaml code from its own sources.
Therefore, the standard bootstrap build process of F\* involves the following three steps:

  **Step 1.** Build F\* using the OCaml compiler from the (possibly outdated) checked-in generated OCaml snapshot.

  **Step 2.** Extract the sources of F\* itself to OCaml using the F\* binary produced at step 1.

  **Repeat step 1**: Rebuild F\* from the newly generated OCaml code in the previous step.

A convenience Makefile target is available to run all three steps:

    $ make boot -j6

If you already compiled F\*, you can do Step 2 then Step 1, by
skipping the first Step 1 (but not its repeat after Step 2) and using
your existing F\* to perform Step 2. To do so, just run `make
dune-bootstrap` instead of `make boot`.

Those rules support parallelism and incrementality (by virtue of the
snapshot being compiled with dune). However, in some cases, it is
necessary to regenerate the whole snapshot by fully erasing it before
extracting it again. This may be needed for instance if some modules
in the F\* sources or in the standard library are renamed or
deleted. To this end, you can use `make dune-full-bootstrap` instead
of `make boot`. This command does `make clean-full-dune-snapshot` to
erase the extracted snapshot.

### Step 1. Build an F\* binary from OCaml snapshot ###

[Get an F\* binary using the OCaml build process](#building-f-and-its-libraries):

    $ make -j6

### Step 2. Extract the sources of F\* itself to OCaml ###

1. Make sure you follow the instructions above to get a
   [working OCaml setup](#prerequisites-working-ocaml-setup).

2. Once you satisfy the prerequisites for your platform,
   translate the F\* sources to OCaml using F\* by running:

        $ make dune-extract-all -j6

### Repeat [Step 1](#step-1-build-an-f-binary-from-ocaml-snapshot)
