Prerequisites for building F* from sources (work in progress)

At the moment:

  - On Windows 8 with .NET framework 4.5 and F# v3.0 :

  - Either: 

      -- Using VisualStudio 2012, open FStar/VS/FStar.sln and build
         solution.

  - or, with Cygwin's GNU make (4.0), run "make" from FStar/src

  On Linux using Mono:

    -- Install mono and fsharp
      -- On Debian/Ubuntu
         $sudo apt-get install mono-complete fsharp

    -- Import certificates
       $ mozroots --import --sync

    -- Install Z3 4.3.1 from sources
    
    -- Run
      $ source setenv.sh
      $ make -C src
