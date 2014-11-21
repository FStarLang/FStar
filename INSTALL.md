Prerequisites for building F* from sources (work in progress)

At the moment:

- On Windows 7/8 with .NET framework 4.5 and F# v3.0 :
  - Either using VisualStudio 2013, open FStar/VS/FStar.sln and build solution.
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

  - Get Z3 4.3.2 binary from here:
    https://z3.codeplex.com/releases/view/101911
    and add it to your PATH.
    For instance, for a 64bit architecture you can do

          $ wget "https://download-codeplex.sec.s-msft.com/Download/Release?ProjectName=z3&DownloadId=891122&FileTime=130523828556400000&Build=20941" -O z3-4.3.2.5a45711f22d9-x64-ubuntu-13.10.zip
          $ unzip z3-4.3.2.5a45711f22d9-x64-ubuntu-13.10.zip
          $ export PATH=z3-4.3.2.5a45711f22d9-x64-ubuntu-13.10/bin:$PATH

  - Compile F* from sources

          $ git clone https://github.com/FStarLang/FStar.git
          $ cd FStar
          $ make -C src

  - Try out

          $ source setenv.sh
          $ mono bin/fstar.exe --prims lib/prims.fst examples/unit-tests/utils.fst
          $ mono bin/fstar.exe --prims lib/prims.fst examples/unit-tests/rec.fst
          $ make test -C src


# To build the OCaml backend

0. Install OCaml (version 4.01.x or 4.02.x)
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

6. Compile it (in src):

        make
        make ocaml.built
        cd ocaml-output
        make parser
        touch .depend
        make depend
        make
