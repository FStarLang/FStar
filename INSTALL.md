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
          $ ln -s z3 z3.exe

  - Compile F* from sources

          $ git clone https://github.com/FStarLang/FStar.git
          $ cd FStar
          $ source setenv.sh
          $ make -C src

  - Try out

          $ mono bin/fstar.exe --prims lib/prims.fst examples/unit-tests/utils.fst
          $ mono bin/fstar.exe --prims lib/prims.fst examples/unit-tests/rec.fst
