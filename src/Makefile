# -*- Makefile -*-

FSTAR_HOME=..
include gmake/z3.mk    # This pins $(Z3) ...
include gmake/fstar.mk # and $(FSTAR) for all sub-make calls

# --------------------------------------------------------------------
BIN=../bin

# --------------------------------------------------------------------
# Configuration of some platform-specific tools; eventually we will want a configure script

ifeq ($(OS),Windows_NT)
  MSBUILD = ./msbuild.bat
  RUNTIME =
  SCONS = scons.bat
else
  # If can't find msbuild, use xbuild, but throw a warning
  MSBUILD = $(shell which msbuild || (echo '\n\n\033[0;31mWarning:\033[0m could not find "msbuild", trying (deprecated) "xbuild"\n\n'>&2; which xbuild))
  RUNTIME = mono
  SCONS = scons
endif

CONFIGURATION?=Release

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
	$(DOS2UNIX) parser/parse.fsi
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
	+$(MAKE) fsharp-regressions
	+$(MAKE) boot-ocaml
	+$(MAKE) clean_extracted #ensures that there is no leftover from previous extraction
	+$(MAKE) fstar-ocaml
	+$(MAKE) ocaml-regressions

# The regressions to be run with a working F# build of F*
fsharp-regressions:
ifeq ($(OS),Windows_NT)
	$(RUNTIME) $(BIN)/tests.exe
else
	@# On Linux, we need to increase the maximum stack size, or we overflow
	ulimit -s unlimited; $(RUNTIME) $(BIN)/tests.exe
endif

ocaml-regressions:
	$(BIN)/tests.exe

# Getting parallelism from this target
uregressions: fstarlib ulib tutorial uexamples interactive-test

# Getting parallelism from this target as well
uregressions-ulong: uregressions ulib-extra

ulib-extra:
	+$(MAKE) -C ../ulib extra

fstarlib:
	+$(MAKE) -C ../ulib/ml

ulib:
	+$(MAKE) -C ../ulib

tutorial: fstarlib
	+$(MAKE) -C ../doc/tutorial regressions

uexamples: fstarlib
	+$(MAKE) -C ../examples all

# Interactive mode regressions
interactive-test:
	$(MAKE) -C tests/interactive

ulong:
	+$(MAKE) utest-prelude
	+$(MAKE) uregressions-ulong

ctags:
	ctags --exclude=boot_fsts --exclude=boot_fstis --exclude=ocaml-output -R .
