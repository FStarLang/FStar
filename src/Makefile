# -*- Makefile -*-

FSTAR_HOME=..
include gmake/z3.mk    # This pins $(Z3) ...
include gmake/fstar.mk # and $(FSTAR) for all sub-make calls

# --------------------------------------------------------------------
BIN=../bin

# --------------------------------------------------------------------
# Configuration of some platform-specific tools; eventually we will want a configure script

ifeq ($(OS),Windows_NT)
  MSBUILD = $(shell cygpath -u \"$$(reg.exe query 'HKLM\SOFTWARE\Microsoft\MSBuild\ToolsVersions\14.0' /v MSBuildToolsPath | tail -n 2 | head -n 1 | sed 's/.*REG_SZ\s\+//g' | tr -d '\r')\")/MSBuild.exe
  RUNTIME =
  SCONS = scons.bat
else
  # If can't find msbuild, use xbuild, but throw a warning
  MSBUILD = $(shell which msbuild || (echo '\n\n\033[0;31mWarning:\033[0m could not find "msbuild", trying (deprecated) "xbuild"\n\n'>&2; which xbuild))
  RUNTIME = mono
  SCONS = scons
endif

CONFIGURATION=Release

MSBUILD := $(MSBUILD) /verbosity:minimal /p:Configuration=$(CONFIGURATION)
DOS2UNIX=$(shell which dos2unix >/dev/null 2>&1 && echo dos2unix || echo true)

# --------------------------------------------------------------------
.SUFFIXES:
MAKEFLAGS += --no-builtin-rules

# parse MAKEFLAGS to extract out the '-jN' switch, and pass it to scons
SCONSFLAGS=$(filter -j%,$(MAKEFLAGS))

.PHONY: all clean boot ocaml nuget-restore nuget-clean

# --------------------------------------------------------------------
# An artefact of the build process is that parse.fsi is auto-generated
all: nuget-restore
	$(MAKE) -C VS install-packages
	$(MSBUILD) VS/FStar.sln
	$(DOS2UNIX) parser/boot/parse.fsi
	chmod a+x $(BIN)/tests.exe
	chmod a+x $(BIN)/fstar.exe

# SAD! Can't make clean if fslex and fsyacc haven't be restored... what...
clean: clean-ocaml nuget-restore
	$(MSBUILD) /t:clean VS/FStar.sln

# --------------------------------------------------------------------

nuget-restore:
	$(RUNTIME) VS/.nuget/NuGet.exe restore VS/FStar.sln

nuget-clean:
	rm -r VS/packages

$(FSYACC) $(FSLEX): nuget-restore

boot:
	$(SCONS) $(SCONSFLAGS) --target=boot

clean_boot:
	$(SCONS) $(SCONSFLAGS) -c --target=boot

clean_extracted:
	$(SCONS) $(SCONSFLAGS) -c --target=ocaml-output

ocaml:
	$(SCONS) $(SCONSFLAGS) --target=extract

boot-ocaml:
	$(SCONS) $(SCONSFLAGS) --target=ocaml-output

clean-ocaml:
	$(SCONS) $(SCONSFLAGS) -c --target=extract

fstar-ocaml:
	$(SCONS) $(SCONSFLAGS) --target=extract
	$(SCONS) $(SCONSFLAGS) --target=ocaml-output

# Fastest way to refresh the snapshot (if it works)
ocaml-fstar-ocaml:
	$(SCONS) $(SCONSFLAGS) --target=ocaml-output
	$(SCONS) $(SCONSFLAGS) --target=extract
	$(SCONS) $(SCONSFLAGS) --target=ocaml-output

# --------------------------------------------------------------------
# Testing
# --------------------------------------------------------------------
OTHERFLAGS+=--hint_info

utest:
	+$(MAKE) utest-prelude
	+$(MAKE) uregressions

# The first tests have to be performed sequentially (but each one may use some parallelism)
utest-prelude:
	+$(MAKE) all
ifeq ($(OS),Windows_NT)
	+$(MAKE) fsharp-regressions #normalizer failures on linux so only run on windows
endif
	+$(MAKE) boot-ocaml
	+$(MAKE) clean_extracted #ensures that there is no leftover from previous extraction
	+$(MAKE) fstar-ocaml

# Interactive mode regressions
interactive-test:
	$(MAKE) -C tests/interactive

# The regressions to be run with a working F# build of F*
fsharp-regressions:
	$(RUNTIME) $(BIN)/tests.exe

#a basic regression test for extraction
#In particular, this test builds fstarlib.cmxa, so
#any other examples that do need fstarlib.cmxa should depend on it
hello:
	+$(MAKE) -C ../examples/hello ocaml

# Getting parallelism from this target
uregressions: hello ulib tutorial uexamples extraction-examples native_tactics interactive-test

# Getting parallelism from this target as well
uregressions-ulong: uregressions ulib-extra

ulib-extra:
	+$(MAKE) -C ../ulib extra

ulib:
	+$(MAKE) -C ../ulib

# Depends on fstarlib.cmxa, which is built by hello
tutorial: hello
	+$(MAKE) -C ../doc/tutorial regressions

# Depends on fstarlib.cmxa, which is built by hello
native_tactics: hello
	+$(MAKE) -C ../examples/native_tactics all

extraction-examples: hello
	+$(MAKE) -C ../examples/extraction all

uexamples:
	+$(MAKE) -C ../examples all

ulong:
	+$(MAKE) utest-prelude
	+$(MAKE) uregressions-ulong

ctags:
	ctags --exclude=boot_fsts --exclude=boot_fstis --exclude=ocaml-output -R .
