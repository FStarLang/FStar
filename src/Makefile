# -*- Makefile -*-

FSTAR_HOME=..
include gmake/z3.mk    # This pins $(Z3) ...
include gmake/fstar.mk # and $(FSTAR) for all sub-make calls

# --------------------------------------------------------------------
BIN=../bin

# --------------------------------------------------------------------
# Configuration of some platform-specific tools; eventually we will want a configure script

ifeq ($(OS),Windows_NT)
  FSC     = fsc
  MSBUILD = $(shell cygpath -u \"$$(reg.exe query 'HKLM\SOFTWARE\Microsoft\MSBuild\ToolsVersions\14.0' /v MSBuildToolsPath | tail -n 2 | head -n 1 | sed 's/.*REG_SZ\s\+//g' | tr -d '\r')\")/MSBuild.exe
  UNAME   = Windows_NT
  FSTAR   = ../bin/fstar.exe
  RUNTIME =
else
  FSC     = fsharpc
  # If can't find msbuild, use xbuild, but throw a warning
  MSBUILD = $(shell which msbuild || (echo '\n\n\033[0;31mWarning:\033[0m could not find "msbuild", trying (deprecated) "xbuild"\n\n'>&2; which xbuild))
  UNAME   = $(shell uname -s)
  FSTAR   = ../bin/fstar-any.sh
  RUNTIME = mono
endif

CONFIGURATION=Release

MSBUILD := $(MSBUILD) /verbosity:minimal /p:Configuration=$(CONFIGURATION)
DOS2UNIX=$(shell which dos2unix >/dev/null 2>&1 && echo dos2unix || echo true)

ifeq ($(UNAME),Darwin)
  HEAD=ghead
  SED=gsed
  FIND=gfind
else
  HEAD=head
  SED=sed
  FIND=find
endif

# --------------------------------------------------------------------

FSLYDIR := VS/packages/FsLexYacc.6.1.0
FSYACC  := $(RUNTIME) $(FSLYDIR)/build/fsyacc.exe
FSLEX   := $(RUNTIME) $(FSLYDIR)/build/fslex.exe

# --------------------------------------------------------------------
.SUFFIXES:
MAKEFLAGS += --no-builtin-rules

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
	$(SCONS) --target=boot

clean_boot:
	$(SCONS) -c --target=boot

clean_extracted:
	$(SCONS) -c --target=ocaml-output

ocaml:
	$(SCONS) --target=extract

boot-ocaml:
	$(SCONS) --target=ocaml-output

clean-ocaml:
	$(SCONS) -c --target=extract

fstar-ocaml:
	$(SCONS) --target=extract
	$(SCONS) --target=ocaml-output

# Fastest way to refresh the snapshot (if it works)
ocaml-fstar-ocaml:
	$(SCONS) --target=ocaml-output
	$(SCONS) --target=extract
	$(SCONS) --target=ocaml-output

# --------------------------------------------------------------------
# Testing
# --------------------------------------------------------------------
OTHERFLAGS+=--hint_info

utest:
	+$(MAKE) all
ifeq ($(OS),Windows_NT)
	+$(MAKE) fsharp-regressions #normalizer failures on linux so only run on windows
endif
	+$(MAKE) boot-ocaml
	+$(MAKE) clean_extracted #ensures that there is no leftover from previous extraction
	+$(MAKE) fstar-ocaml
	+$(MAKE) uregressions

# Interactive mode regressions
interactive-test:
	$(MAKE) -C tests/interactive

# The regressions to be run with a working F# build of F*
fsharp-regressions:
	$(RUNTIME) $(BIN)/tests.exe

#a basic regression test for extraction
hello:
	+$(MAKE) -C ../examples/hello ocaml

# Getting parallelism from this target
uregressions: hello ulib tutorial uexamples interactive-test

ulib:
	+$(MAKE) -C ../ulib

tutorial: ulib
	+$(MAKE) -C ../doc/tutorial regressions

native_tactics: ulib
	+$(MAKE) -C ../examples/native_tactics all

uexamples:
	+$(MAKE) -C ../examples all

ulong:
	+$(MAKE) utest
	+$(MAKE) -C ../ulib extra

ctags:
	ctags --exclude=boot_fsts --exclude=boot_fstis --exclude=ocaml-output -R .
