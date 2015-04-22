### Binary releases ###

- https://github.com/FStarLang/FStar/releases

### Building F* from sources ###

#### On Windows 7/8 using Visual Studio ####

  - Prerequisite: .NET framework 4.5

  - Prerequisite: [VisualStudio 2013 and Visual F# Tools (v3.0 or later)](http://fsharp.org/use/windows/)
    - for instance install the **free**
      [Visual Studio 2013 Community](https://www.visualstudio.com/en-us/products/visual-studio-community-vs.aspx)
    - Install the Visual F# Tools from Microsoft
      (by clicking the "Get Visual F# Tools for Visual Studio 2013"
       link [here](https://msdn.microsoft.com/en-us/vstudio/hh388569.aspx))

  - Using VisualStudio 2013, open `FStar/VS/FStar.sln` and build solution.

  - Get a Z3 4.3.2 binary and add it to your PATH
    - 64 bits: https://z3.codeplex.com/releases/view/135729
    - 32 bits: https://z3.codeplex.com/releases/view/135728

#### On Linux or Mac OS X using Mono ####

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

### Bootstrapping the compiler in OCaml ###

#### Windows Prerequisites ####

0. Use Visual Studio for building `fstar.exe` as describes above
   (note: running cygwin/wodi `make` in `src` will probably
   just give you a broken binary).

1. Use [Wodi] for installing OCaml (version 4.01.0 or newer)

2. [Wodi] also installs Cygwin; when your asked which Cygwin packages
   you want add `git` to the default list. If you forgot to do this,
   you can still do that by downloading [Cygwin]'s setup-x86.exe and
   pointing it at your wodi install. By installing [Wodi] you get a
   special Cygwin terminal where you should run all the commands below.

3. Use the [Wodi] ocaml package manager to install `batteries`; you can
   do this either from the visual package manager or by issuing the
   command `godi_add godi-batteries` in the Wodi's Cygwin terminal.

[Wodi]: http://wodi.forge.ocamlcore.org/
[Cygwin]: https://www.cygwin.com/

#### Linux/MacOS Prerequisites ####

0. OCaml (version 4.01.0 or later)
   - Can be installed using either your package manager or using OPAM (see below).

1. OPAM (version 1.2.x).
   - Installation instructions available at various places
     (e.g., https://github.com/realworldocaml/book/wiki/Installation-Instructions#getting-opam
     or http://opam.ocaml.org/doc/Install.html).
     You need to initialize it by running `opam init` and update the `PATH`
     variable to the `ocamlfind` and the OCaml libraries. If you allow
     `opam init` to edit your `~/.bashrc` or `~/.profile`, it is done
     automatically; otherwise, use: `eval $(opam config env)`.

2. Install OCaml Batteries using OPAM:

        $ opam install batteries

#### Bootstrapping the compiler in OCaml ####

- Once you satisfy the prerequisites for your platform,
  generate the OCaml backend by running the following commands in `src`:

        $ make
        $ make ocaml

### Creating binary packages for your platform ###

(no cross platform compilation supported at the moment)

0. Make sure you have the Z3 binary in your `<fstar-home>/bin` folder
   (this prerequisite could go away at some point)

1. Bootstrap the compiler in OCaml using the instructions above

2. Run the following commands in `src/ocaml-output`:

        $ make parser
        $ make
        $ make package
