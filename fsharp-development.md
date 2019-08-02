# Building F*, taking the F# route

F\* is written in a subset of F# that F\* itself can also parse with a special flag. Although the OCaml extraction route outlined in INSTALL.md is the preferred route, F\* can also be built using the F# extraction route:

**Step 1.** Build F\* from sources using the F# compiler (obtaining a .NET binary for F\*).

**Step 2.** Extract the sources of F\* itself to OCaml using the F\* binary produced at step 1.

**Step 3.** Re-build F\* using the OCaml compiler from the code generated at step 2 (obtaining a faster native binary for F\*).

Steps 2 and 3 are documented in INSTALL.md.

### Building F\* from sources using the F# compiler ###

#### On Windows 7/8/10 ####

  - Prerequisite: .NET framework 4.5

  - Prerequisite: Visual Studio 2017 and its integrated [Visual F# Tools for F# 4.1](http://fsharp.org/use/windows/)
    - for instance install the **free**
      [Visual Studio Community](https://www.visualstudio.com/en-us/products/visual-studio-community-vs.aspx)
    - The Visual F# Tools are installed automatically when you first
      create or open an F# project.

**Easy alternative:** open a Cygwin command prompt, and run `make`
from the `src` directory. This will run `msbuild` on the Visual Studio
solution file; in effect, this performs exactly what you would get by
clicking the "Build" button within Visual Studio.

Read on for the more complete solution involving Visual Studio itself.

  - Run the `src/VS/nuget-restore.bat` script _from the top-level F\* directory_
    before opening the solution for the first time.
    F\* depends upon NuGet packages that are incompatible with
    Visual Studio's internal invocation of NuGet's restore feature.

        C:\Users\xxx\Desktop\FStar>src\VS\nuget-restore.bat
        Installing 'FsLexYacc.Runtime 6.1.0'.
        Installing 'FsLexYacc 6.1.0'.
        Successfully installed 'FsLexYacc.Runtime 6.1.0'.
        Successfully installed 'FsLexYacc 6.1.0'.
        All packages listed in packages.config are already installed.

  - Using Visual Studio, open `src/VS/FStar.sln` and build the solution
    (in the menus: Build > Build Solution). **Make sure to choose the 'Release' configuration**.
    Note: the 'Debug' configuration may be the default, although it has no optimizations enabled
    and is not capable of bootstrapping.

**Note:** If Visual Studio fails to open one or more projects, the
  problem is likely that the NuGet package cache hasn't been
  restored. You must either exit Visual Studio to restore the cache
  (using the `src/VS/nuget-restore.bat` script), or restart Visual
  Studio after having restored the cache. Otherwise, F\* may not
  successfully build (or correctly build).

#### On Linux or Mac OS X using Mono ####

  - Install mono (any version from 4.0.3.0 to 5.14.x),
            fsharp (version 4.1.x, where [on Linux x<=18](https://github.com/FStarLang/FStar/issues/1539)), and
            msbuild (version 14.1.x-15.8.x)

    - On Debian/Ubuntu

            $ sudo apt-get install mono-complete fsharp

    - On Arch

            $ pacman -S mono
            $ aura -A msbuild-stable
            $ git clone https://github.com/catalin-hritcu/arch-fsharp.git
            $ cd arch-fsharp
            $ git checkout fsharp-4.1.18
            $ makepkg
            $ pacman -U fsharp-4.1.18-1-any.pkg.tar.xz

    - For other Linux distributions check out these links:
      - http://www.mono-project.com/download/#download-lin
      - http://fsharp.org/use/linux/
      - https://github.com/Microsoft/msbuild

    - For Mac OS X use HomeBrew or install the MRE:
      - http://www.mono-project.com/download/#download-mac

  - Compile F\* from sources

          $ git clone https://github.com/FStarLang/FStar.git
          $ cd FStar
          $ make -C src

  - Try out binary using [the instructions above](https://github.com/FStarLang/FStar/blob/master/INSTALL.md#testing-a-binary-package).

  - Another thing you can try is bootstrapping the F\* compiler:

          $ export PATH=/path/to/fstar/bin:$PATH
          $ make -C src boot

    If `make boot` causes a stack overflow try issuing `ulimit -s unlimited` in the terminal beforehand.

Note: you may want to make the `PATH` change permanent by adding:

```
export PATH=/path/to/fstar/bin:$PATH
```

into your `~/.bashrc`.