### Binary releases ###

- https://github.com/FStarLang/FStar/releases

### Building F* from sources (.NET version) ###

F* is written in a subset of F# that F* can also parse with a special flag.
Therefore, the build process of F* is as follows:

- build F* using the F# compiler
- compile the source of F* with F* and emit OCaml code (optional)
- re-build F* using the OCaml compiler (optional).

The first step builds an F* compiler that runs on .NET. The last two steps build
a native, more optimized binary of F*.

#### On Windows 7/8 using Visual Studio ####

  - Prerequisite: .NET framework 4.5

  - Prerequisite: [VisualStudio 2013 and Visual F# Tools (v3.0 or later)](http://fsharp.org/use/windows/)
    - for instance install the **free**
      [Visual Studio 2013 Community](https://www.visualstudio.com/en-us/products/visual-studio-community-vs.aspx)
    - Install the Visual F# Tools from Microsoft
      (by clicking the "Get Visual F# Tools for Visual Studio 2013"
       link [here](https://msdn.microsoft.com/en-us/vstudio/hh388569.aspx))

  - Using VisualStudio 2013, open `FStar/VS/FStar.sln` and build solution (in
      the menus: Build > Build Solution).

  - Get a Z3 4.3.2 binary and add it to your PATH
    - 64 bits: https://z3.codeplex.com/releases/view/135729
    - 32 bits: https://z3.codeplex.com/releases/view/135728

Please note that 1) the Makefile is currently broken on Windows, and 2) the
"Release" build configuration is also broken in Visual Studio.

#### On Linux or Mac OS X using Mono ####

  - Install mono 3.10.x or 3.12.x and fsharp 3.1.x

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

  - Import certificates for Mono

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

  - If `make test.net` (`make boot` in fact) causes stack overflow try
    issuing `ulimit -s unlimited` in the terminal beforehand.


### Building F* (native binary via OCaml) ###

Once the .NET version of F* has been built using the F# compiler, an optional
step is to translate the sources of F* into OCaml (using F*) and compile that
output with OCaml to get a faster, native binary.

The current version of F* requires OCaml 4.02.

#### Instructions for Windows ####

0. Follow the steps above to compile the .NET version of F*.

1. Since WODI has been discontinued, the only solution is to use the [OCaml
   Installer for Windows](http://protz.github.io/ocaml-installer/). This
   installer installs an outdated version of OCaml (4.01.0) -- this is going to
   cause some difficulties.

2. Install Batteries from source. The current release of Batteries does *not*
   compile with 4.01.0, so you need to build an older version. Open up a cygwin
   shell and:
      * `git clone https://github.com/ocaml-batteries-team/batteries-included`
      * `cd batteries-included`
      * `git checkout v2.2.0`
      * `make && make install`

3. Translate the F* sources from F# to OCaml using F*.
      * `cd fstar/src`
      * `make ocaml`

4. Generate the parser
      * `cd ocaml-output`
      * `make parser`

5. Patch the `support.ml` file because it no longer compiles with 4.01.0
      * at the beginning of the file, add `module S = String`
      * at line 1285, replace `Bytes.create maxlen` with
        `S.make maxlen ' '`
      * replace the next three occurrences of `Bytes` with `S`

6. Finish the build
      * `make`

(Side note: this procedure generates a native F* binary , that is, a binary that
does *not* depend on `cygwin1.dll`, as since the installer above uses a
*native* Windows port of OCaml.  Cygwin is just there to provide `make` and
other utilities required for the build.)

#### Instructions for Linux and Mac OS X ####

0. Build the .NET version of F* using the instructions above.

0. Install OCaml (version 4.02.0 or later)
   - Can be installed using either your package manager or using OPAM
     (see below).

1. Install OPAM (version 1.2.x).
   - Installation instructions available at various places
     (e.g., https://github.com/realworldocaml/book/wiki/Installation-Instructions#getting-opam
     or http://opam.ocaml.org/doc/Install.html).
     You need to initialize it by running `opam init` and update the `PATH`
     variable to the `ocamlfind` and the OCaml libraries. If you allow
     `opam init` to edit your `~/.bashrc` or `~/.profile`, it is done
     automatically; otherwise, use: `eval $(opam config env)`.

2. Install OCaml Batteries using OPAM:

        $ opam install batteries

1. Once you satisfy the prerequisites for your platform,
   first generate a set of files in OCaml syntax
   by running the following commands in `$FSTAR_HOME/src`:

        $ make ocaml

2. Then run the following commands in `src/ocaml-output`:

        $ make parser
        $ make

### Creating binary packages for your platform ###

(no cross-platform compilation supported at the moment)

0. Bootstrap the compiler in OCaml using the instructions above

1. Make sure you have the Z3 binary in your `$PATH` or
   in the `$FSTAR_HOME/bin` directory

2. Run the following command in `src/ocaml-output`:

        $ make package

3. Test that the binary is good by expanding the archive and running
   `make` in the `examples` directory inside
