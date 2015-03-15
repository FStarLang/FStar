### Binary releases
- https://github.com/FStarLang/FStar/releases

### Building F* from sources

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
          $ make test -C src

  - If `make test` (`make boot` in fact) causes stack overflow try
    issuing `ulimit -s unlimited` in the terminal beforehand.

### Bootstrapping the compiler in OCaml

0. Prerequisite: OCaml (version 4.01.0 or newer)

1. Prerequisite: OPAM (version 1.2.x).
   - Installation instructions available at various places
     (e.g., https://github.com/realworldocaml/book/wiki/Installation-Instructions#getting-opam
     or http://opam.ocaml.org/doc/Install.html).
     You need to initialize it by running `opam init` and update the `PATH`
     variable to the `ocamlfind` and the OCaml libraries. If you allow
     `opam init` to edit your `~/.bashrc` or `~/.profile`, it is done
     automatically; otherwise, use: `eval $(opam config env)`.

2. Install OCaml Batteries:

        $ opam install batteries

3. Generate the OCaml backend by running the following commands in `src`:

        $ make
        $ make ocaml

### Creating binary packages for your platform

(no cross platform compilation supported at the moment)

0. Make sure you have the Z3 binary in your `<fstar-home>/bin` folder (this prerequisite could go away at some point)

1. Bootstrap the compiler in OCaml using the instructions above

2. Run the following commands in `src/ocaml-output`:

        $ make parser
        $ make
        $ make package

#### Additional instructions for getting Windows binaries

Use [wodi](http://wodi.forge.ocamlcore.org/) for building the package. Make sure you have F# installed and fsc.exe is in your PATH. To install F# [check this out](http://fsharp.org/use/windows/).
