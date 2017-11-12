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
  MSBUILD = ./msbuild.bat
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

CONFIGURATION?=Release

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

# --------------------------------------------------------------------
# Bootstrapping in OCaml
# --------------------------------------------------------------------

# This is the way in which we invoke F* for boostrapping
#   -- we use automatic dependence analysis based on files in ulib, src/{basic, ...} and boot
#   -- eager_inference, MLish, lax: all tune type-inference for use with unverified ML programs
INCLUDE_PATHS = \
	../ulib \
	boot \
	basic \
	extraction \
	format \
	fsdoc \
	fstar \
        parser \
	prettyprint \
	reflection \
	smtencoding \
	syntax \
        tactics \
	tosyntax \
	typechecker \
	tests

FSTAR_C=$(FSTAR) $(OTHERFLAGS) --cache_checked_modules --eager_inference --lax --MLish --no_location_info \
		   --odir ocaml-output $(addprefix --include , $(INCLUDE_PATHS))

EXTRACT_MODULES=FStar.Pervasives FStar.Common FStar.Range		\
		FStar.Options FStar.Ident FStar.Errors FStar.Const	\
		FStar.Format FStar.Order FStar.Dependencies		\
		FStar.Interactive.CompletionTable			\
		FStar.Interactive.Ide FStar.Interactive.Legacy		\
		FStar.Universal FStar.Indent FStar.Main

EXTRACT_NAMESPACES=FStar.Extraction FStar.Fsdoc FStar.Parser		\
		   FStar.Reflection FStar.SMTEncoding FStar.Syntax	\
		   FStar.Tactics FStar.Tests FStar.ToSyntax		\
		   FStar.TypeChecker

NO_EXTRACT=FStar.Tactics.Native FStar.Tactics.Load	\
           FStar.Extraction.ML.PrintML

EXTRACT = $(addprefix --extract_module , $(EXTRACT_MODULES))		\
	  $(addprefix --extract_namespace , $(EXTRACT_NAMESPACES))	\
	  $(addprefix --no_extract , $(NO_EXTRACT))


FSTARBOOT = $(FSTAR_C) --expose_interfaces --codegen OCaml

# --------------------------------------------------------------------------------
# Preparing for bootstrapping by copying and sed'ing a few F# files
# --------------------------------------------------------------------------------
ALL_BOOT=$(addprefix boot/FStar., \
           Util.fsti List.fsti Bytes.fsti String.fsti BigInt.fsti \
		   Pprint.fsti Parser.Parse.fsti \
		   Tactics.Interpreter.fst Tactics.Interpreter.fsti \
           Tests.Test.fst)

boot/%.fsti: basic/boot/%.fsi | boot_dir
	cp $^ $@
	$(SED) -i 's/<.* when .* : equality>//g' $@
	$(SED) -i '/\/\/ *JUST *FSHARP */d' $@

boot/%.fsti: prettyprint/boot/%.fsi | boot_dir
	cp $^ $@
	$(SED) -i '/\/\/ *JUST *FSHARP */d' $@

#fix up a use of polymorphic recursion in F#, which has a different syntax than F*
boot/FStar.Tactics.Interpreter.fst: tactics/boot/FStar.Tactics.Interpreter.fs | boot_dir
	cp $^ $@
	$(SED) -i '/\/\/ *JUST *FSHARP */d' $@
	$(SED) -i 's,^ *// *IN *F\* *:,,g' $@

boot/FStar.Tests.Test.fst: tests/boot/FStar.Tests.Test.fs | boot_dir
	cp $^ $@
	$(SED) -i '/\/\/ *JUST *FSHARP */d' $@

boot/FStar.Parser.Parse.fsti: parser/parse.fsi | boot_dir
	echo "#light \"off\"" > $@
	$(HEAD) -n -12 $^ >> $@
	$(SED) -i 's/module FStar.Parser.Parse/module FStar.Parser.Parse\nopen FStar.All\nopen FStar.BaseTypes\ntype bytes = array<byte>\nopen FStar.Syntax.Syntax/' $@

boot/%.fst: basic/boot/%.fs | boot_dir
	cp $^ $@

boot/FStar.Parser.Parse.fst: parser/parse.fs | boot_dir
	cp $^ $@

boot/FStar.Tactics.Interpreter.fsti: tactics/boot/FStar.Tactics.Interpreter.fsi | boot_dir
	cp $^ $@

boot_dir:
	mkdir -p boot

boot: $(ALL_BOOT)

clean_boot:
	rm -rf boot

# --------------------------------------------------------------------------------
# End preparing for bootstrap
# --------------------------------------------------------------------------------

clean_extracted:
	rm -f ocaml-output/FStar_*.ml

ocaml: boot
	+$(MAKE) all-ml

boot-ocaml:
	+$(MAKE) -C ocaml-output all

clean-ocaml: clean_boot
	+$(MAKE) -C ocaml-output clean

fstar-ocaml: ocaml
	+$(MAKE) boot-ocaml

# Fastest way to refresh the snapshot (if it works)
ocaml-fstar-ocaml: boot-ocaml
	+$(MAKE) ocaml
	+$(MAKE) boot-ocaml


%.checked.lax: %
	$(FSTAR_C) $*
	touch $@

ocaml-output/%.ml:
	$(FSTAR_C) $(subst .checked.lax,,$<) --codegen OCaml --extract_module $(basename $(notdir $(subst .checked.lax,,$<)))

# --------------------------------------------------------------------
# Dependency analysis for bootstrapping
# --------------------------------------------------------------------

depend: .depend
	$(FSTAR_C) --dep full fstar/FStar.Main.fs boot/FStar.Tests.Test.fst $(EXTRACT) --codegen OCaml > .depend

include .depend

all-ml: $(ALL_ML_FILES)


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

