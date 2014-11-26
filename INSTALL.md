# Binary releases
- https://github.com/FStarLang/FStar/releases

# Building F* from sources

- On Windows 7/8 with .NET framework 4.5 and F# v3.0 :
  - Either using VisualStudio 2013, open FStar/VS/FStar.sln and build solution.
  - or, with Cygwin's GNU make (4.0), run "make" from FStar/src

- On Linux or Mac OS X using Mono:
  - Install mono 3.10.x and fsharp 3.1.x
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

          $ wget "https://download-codeplex.sec.s-msft.com/Download/Release?ProjectName=z3&DownloadId=891122&FileTime=130523828556400000&Build=20941" -O z3-4.3.2.5a45711f22d9-x64-ubuntu-13.10.zip
          $ unzip z3-4.3.2.5a45711f22d9-x64-ubuntu-13.10.zip
          $ export PATH=z3-4.3.2.5a45711f22d9-x64-ubuntu-13.10/bin:$PATH

    - On Mac OS X get binary from here:
      - https://z3.codeplex.com/releases/view/101918

  - Compile F* from sources

          $ git clone https://github.com/FStarLang/FStar.git
          $ cd FStar
          $ make -C src

  - Try out

          $ source setenv.sh
          $ mono bin/fstar.exe --prims lib/prims.fst examples/unit-tests/utils.fst
          $ make test -C src

  - If `make test` (`make boot` in fact) causes stack overflow try
    issuing `ulimit -s unlimited` in the terminal beforehand.

# Bootstrapping the compiler in OCaml

0. Prerequisite: OCaml (version 4.01.0 or newer)

1. Prerequisite: OPAM (version 1.2.x).
   - Installation instructions available at various places
     (e.g., https://github.com/realworldocaml/book/wiki/Installation-Instructions#getting-opam
     or http://opam.ocaml.org/doc/Install.html).
     You need to initialize it by running `opam init` and update the `PATH`
     variable to the `ocamlfind` and the OCaml libraries. If you allow
     `opam init` to edit your `~/.bashrc` or `~/.profile`, it is done
     automatically; otherwise, use: `eval $(opam config env)`.

2. Install the required OCaml libraries:

        $ opam install batteries camlp4 conf-gmp cstruct ctypes fileutils menhir oasis ocaml-data-notation ocamlfind ocamlify ocamlmod ocplib-endian optcomp ounit sexplib sqlite3-ocaml type_conv zarith

3. Compile and install the 3rdparty tools (in src/support/ocaml/3rdparty):

        $ git submodule init
        $ git submodule update
        $ make

4. Compile and install the fstar OCaml package (in src/support/ocaml/fstar-lib):

        $ ./autogen.sh
        $ ./configure
        $ make
        $ make install

   If the `make install` fails with
   `ocamlfind: Package fstar is already installed`
   you need to remove first the previous package then re-run `make install`

        $ ocamlfind remove fstar
        $ make install

5. Generate the backend (in src):

        $ make
        $ make ocaml
