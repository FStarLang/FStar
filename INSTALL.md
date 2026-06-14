## Table of Contents ##

  * [Binary package](#binary-package)
  * [Online editor](#online-editor)
  * [OPAM package](#opam-package)
  * [Running F* from a docker image](#running-f-from-a-docker-image)
  * [Nix Package](#nix-package)
  * [Building F* from the OCaml sources](#building-f-from-the-ocaml-sources)
    * [Prerequisites: Working OCaml setup](#prerequisites-working-ocaml-setup)
      * [Instructions for Windows](#instructions-for-windows)
      * [Instructions for Linux and Mac OS X](#instructions-for-linux-and-mac-os-x)
      * [Instructions for all OSes](#instructions-for-all-oses)
    * [Building F* and the libraries](#building-f-and-its-libraries)
  * [Runtime dependency: Particular version of Z3](#runtime-dependency-particular-version-of-z3)

## Binary package ##

The easiest way to get a recent binary installation of F\* is to use the 
.scripts/install-fstar.sh script.

The simplest way is to run the following command, which will install the latest
weekly binary release for your platform, including the necessary Z3 binaries.

```
curl -fsSL https://aka.ms/install-fstar | bash -s -- --release
```

The installer will instruct you to add the F* installation directory to your path.

You can also manually download the binary of your choice from 
[F\* binaries on GitHub]: https://github.com/FStarLang/FStar/releases

Using a binary package allows you to use F* even if you do not want to
install OCaml on your machine. You will be able to verify F* code, and
to generate OCaml code from F*; but if you want to compile such
generated OCaml code, then you will need OCaml.

### Testing a binary package ###

After installing a F* binary package as described above, you can quickly test
that the binary works on a simple example from the library by doing the following
and observing the expected output shown below.

```
$ fstar.exe -f FStar.List.Tot.Base.fst              
Verified module: FStar.List.Tot.Base
All verification conditions discharged successfully
```

## Online editor ##

You can also try out F\* quickly in your browser by
using the [online F\* editor] that's part of the [F\* tutorial].

[online F\* editor]: https://www.fstar-lang.org/run.php
[F\* tutorial]: https://www.fstar-lang.org/tutorial

## Runtime dependency: Particular version of Z3 ##

If you install from an F* binary package, then it comes with its
own versions of Z3 and you should not need to configure anything
else.

Otherwise, F\* requires specific versions of Z3 to work correctly,
and will refuse to run if the version string does not match.
You should have `z3-4.13.3` in your `$PATH`:

```
❯ z3-4.13.3 --version
Z3 version 4.13.3 - 64 bit
```

On Linux you can install several Z3 versions usable with F* with the following command:
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


## Running F\* from a docker image ##

An alternative to installing binaries is to install a docker image.
We currently provide the following two on docker hub: `fstarlang/fstar-emacs`
with emacs support and `fstarlang/fstar` for purists.
The image is automatically kept up to date through a cloud build.

You only have to install docker and an X server for your platform and you are good to go.
See [Running F\* from a docker image](https://github.com/FStarLang/FStar/wiki/Running-F%2A-from-a-docker-image)
for the details on how to use docker.

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

This builds the F\* compiler (with Pulse support baked in), verifies
the standard library and the Pulse library, and installs the result
into `out/`. You can then add `out/bin` to your `PATH`.

Run `make help` for a list of all available targets.

   **Note:** On Windows this generates a *native* F\* binary, that is,
   a binary that does *not* depend on `cygwin1.dll`, since [the installer above](#instructions-for-windows)
   uses a *native* Windows
   port of OCaml.  Cygwin is just there to provide `make` and other
   utilities required for the build.  This also means that when
   linking C libraries with OCaml compiled objects one needs to use
   the *correct* mingw libraries and *not* the Cygwin ones. OCaml uses
   special `flexlink` technology for this. See `examples/crypto` and
   `contrib/CoreCrypto/ml` for examples.

The build is a multi-stage bootstrapping process (stage0 → stage1 →
stage2 → stage3). For details see [doc/ref/bootstrapping](doc/ref/bootstrapping).
