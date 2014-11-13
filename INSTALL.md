Prerequisites for building F* from sources (work in progress)

At the moment:

- On Windows 8 with .NET framework 4.5 and F# v3.0 :
  - Either using VisualStudio 2012, open FStar/VS/FStar.sln and build solution.
  - or, with Cygwin's GNU make (4.0), run "make" from FStar/src

- On Linux using Mono:
  - Install mono and fsharp
    - On Debian/Ubuntu

            $ sudo apt-get install mono-complete fsharp

    - On Arch

            $ pacman -S mono
            $ aura -A fsharp

  - Import certificates

          $ mozroots --import --sync

  - Install Z3 4.3.1 from sources

          $ wget "https://download-codeplex.sec.s-msft.com/Download/SourceControlFileDownload.ashx?ProjectName=z3&changeSetId=89c1785b73225a1b363c0e485f854613121b70a7" -O z3-4.3.1-89c1785b-src.zip
          $ unzip z3-4.3.1-89c1785b-src.zip -d z3-4.3.1-89c1785b-src
          $ cd z3-4.3.1-89c1785b-src
          $ autoconf
          $ ./configure
          $ python scripts/mk_make.py
          $ cd build
          $ make -j4

  - Compile F* from sources

          $ git clone https://github.com/FStarLang/FStar.git
          $ cd FStar
          $ make -C src

  - Try out

          $ source setenv.sh
          $ mono bin/fstar.exe --prims lib/prims.fst examples/unit-tests/utils.fst
          $ mono bin/fstar.exe --prims lib/prims.fst examples/unit-tests/rec.fst


# To build the OCaml backend

1. Install opam, initialize it (opam init) and update the path to
   ocamlfind and the ocaml libraries
2. Install the following libraries:
     batteries camlp4 conf-gmp cstruct ctypes fileutils menhir oasis
     ocaml-data-notation ocamlfind ocamlify ocamlmod ocplib-endian optcomp
     ounit sexplib sqlite3-ocaml type_conv zarith
   (opam install [...])
3. Compile and install the 3rdparty tools (in
   src/support/ocaml/3rdparty):
     git submodule init
     git submodule update
     make
4. Compile and install the fstar-lib (in src/support/ocaml/fstar-lib):
     ./autogen.sh
     ./configure
     make
     make install
5. Generate the backend (in src):
     make ocaml
6. Compile it:
     ocamlfind ocamlc -package fstar ocaml.ml
