# -*- Makefile -*-

# --------------------------------------------------------------------
LIB=../lib
BIN=../bin
ULIB=../ulib

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
  MSBUILD = xbuild
  UNAME   = $(shell uname -s)
  FSTAR   = ../bin/fstar-any.sh
  RUNTIME = mono
endif

CONFIGURATION=Release
-include Makefile.local

MSBUILD := $(MSBUILD) /verbosity:minimal /p:Configuration=$(CONFIGURATION)

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
.PHONY: all z3_x86 z3_x64 wc clean tidy boot ocaml
.PHONY: msbuild msbuild-clean nuget-restore nuget-clean

# --------------------------------------------------------------------
all: nuget-restore
	$(MAKE) -C VS install-packages
	$(MSBUILD) VS/FStar.sln
	chmod a+x $(BIN)/tests.exe
	chmod a+x $(BIN)/fstar.exe

# SAD! Can't make clean if fslex and fsyacc haven't be restored... what...
clean: nuget-restore
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
#   -- we use automatic dependence analysis based on files in ulib, u_boot_fsts and boot_fstis
#   -- eager_inference, MLish, lax: all tune type-inference for use with unverified ML programs
#   -- fs_typ_app parses list<foo> as valid syntax, for overlap with F# syntax
FSTARBOOT=$(FSTAR) $(OTHERFLAGS) --eager_inference --lax --MLish --no_location_info \
		   --odir u_ocaml-output --codegen OCaml --include ../ulib --include u_boot_fsts --include boot_fstis

# JP: these modules are meant to be fsti's (realized in ML); but, the compiler
# currently works in non-universes mode so this is not possible. These files are
# in ulib/ as fstis, though, so the --no_extract argument will go away once the
# F* compiler bootstraps in universes.

U_BOOT_BASIC_FSTI=$(addprefix boot_fstis/FStar., string.fsti list.fst util.fsti platform.fsti bytes.fst range.fsti version.fsti getopt.fsti unionfind.fsti Pprint.fsti)
U_ALL_INTERFACES=$(U_BOOT_BASIC_FSTI) boot_fstis/FStar.Parser.Parse.fsti

# SI: does it have to go prettyprint.fsti->FStar.Pprint.fsti?
boot_fstis/FStar.Pprint.fsti: prettyprint/prettyprint.fsi
	cp $^ $@

boot_fstis/%.fsti: basic/%.fsi
	cp $^ $@

boot_fstis/FStar.%.fsti: basic/%.fsi
	cp $^ $@

boot_fstis/FStar.list.fst: basic/list.fsi
	cp $^ $@
	$(SED) -i 's/open Prims/module ALL_TEMP = FStar.All/g' $@
	$(SED) -i 's/<.* when .* : equality>//g' $@
	$(SED) -i 's/val/assume val/g' $@

boot_fstis/FStar.bytes.fst: basic/bytes.fsti
	cp $^ $@

boot_fstis/FStar.util.fsti: basic/util.fsi
	cp $^ $@
	$(SED) -i 's/open System.IO/module ALL_TMP = FStar.All/g' $@
	$(SED) -i 's/type time.*/assume new type time/g'  $@
	$(SED) -i 's/type smap.*/assume new type smap : Type0 -> Type0/g'  $@
	$(SED) -i 's/type imap.*/assume new type imap : Type0 -> Type0/g'  $@
	$(SED) -i 's/type out_channel.*/assume new type out_channel/g'  $@
	$(SED) -i 's/type file_handle.*/assume new type file_handle/g'  $@
	$(SED) -i 's/type stream_reader.*/assume new type stream_reader/g'  $@
	$(SED) -i 's/type string_builder.*/assume new type string_builder/g'  $@
	$(SED) -i 's/type proc.*/assume new type proc/g' $@
	$(SED) -i 's/type set.*/assume new type set:Type0 -> Type0/g' $@

boot_fstis/FStar.unionfind.fsti: basic/unionfind.fsi
	cp $^ $@
	$(SED) -i 's/type pa_t.*/module ALL_TMP = FStar.All/g' $@
	$(SED) -i 's/and data.*//g' $@
	$(SED) -i 's/.*| PArray.*//g' $@
	$(SED) -i 's/.*| PDiff.*//g' $@
	$(SED) -i 's/type puf_t.*//g' $@
	$(SED) -i 's/type puf.*/assume new type puf : Type0 -> Type0/g' $@
	$(SED) -i 's/type p_uvar.*/assume new type p_uvar : Type0 -> Type0/g' $@
	$(SED) -i 's/type cell.*//g' $@
	$(SED) -i 's/and contents.*//g' $@
	$(SED) -i 's/.*| Data.*//g' $@
	$(SED) -i 's/.*| Fwd.*//g' $@
	$(SED) -i 's/type uvar.*/assume new type uvar : Type0 -> Type0/g' $@

boot_fstis/FStar.Parser.Parse.fsti: parser/parse.fsi
	echo "#light \"off\"" > $@
	$(HEAD) -n -12 $^ >> $@
	$(SED) -i 's/module FStar.Parser.Parse/module FStar.Parser.Parse\nopen FStar.All\nopen FStar.BaseTypes\ntype bytes = array<byte>/' $@

rename_as_fst:
	./tools/rename_all_boot_fsts
	cp parser/parseit.fsi u_boot_fsts/FStar.Parser.Parseit.fsti

prep: $(U_ALL_INTERFACES)
	make rename_as_fst
	#fix up a use of polymorphic recursion in F#, which has a different syntax than F*
	$(SED) -i 's/^and unembed_tactic_0.*//g' u_boot_fsts/FStar.Tactics.Interpreter.fst
	$(SED) -i 's/^\/\/F\* version: and unembed_tactic_0/and unembed_tactic_0/g' u_boot_fsts/FStar.Tactics.Interpreter.fst

clean_u_extract_ocaml:
	rm -rf boot_fstis u_boot_fsts u_ocaml-output
	mkdir boot_fstis u_boot_fsts u_ocaml-output

u_extract_misc:$(addprefix u_boot_fsts/, FStar.Common.fst FStar.Options.fst FStar.Ident.fst FStar.Errors.fst FStar.Const.fst \
					 FStar.Format.fst)
	$(FSTARBOOT) $^ $(addprefix --extract_module , FStar.Common FStar.Options FStar.Ident FStar.Errors FStar.Const FStar.Format)

u_extract_syntax:$(addprefix u_boot_fsts/FStar.Syntax., Syntax.fst Const.fst Subst.fst Free.fst \
							InstFV.fst Util.fst Print.fst MutRecTy.fst) \
                  u_boot_fsts/FStar.Fsdoc.Generator.fst
	$(FSTARBOOT) $^ --extract_namespace FStar.Syntax --extract_namespace FStar.Fsdoc

u_extract_parser:$(addprefix u_boot_fsts/FStar.Parser., AST.fst Interleave.fst Lexhelp.fst Parseit.fsti Driver.fst Dep.fst ToDocument.fst)
	$(FSTARBOOT) $^ --extract_namespace FStar.Parser

u_extract_normalizer: $(addprefix u_boot_fsts/FStar.TypeChecker., Common.fst Env.fst Normalize.fst Err.fst)
	$(FSTARBOOT) $^ --extract_namespace FStar.TypeChecker

u_extract_rel: u_boot_fsts/FStar.TypeChecker.Rel.fst
	$(FSTARBOOT) $^ --extract_module FStar.TypeChecker.Rel

u_extract_util: u_boot_fsts/FStar.TypeChecker.Util.fst
	$(FSTARBOOT) $^ --extract_module FStar.TypeChecker.Util

u_extract_dmff: u_boot_fsts/FStar.TypeChecker.DMFF.fst
	$(FSTARBOOT) $^ --extract_module FStar.TypeChecker.DMFF

u_extract_tcterm: u_boot_fsts/FStar.TypeChecker.TcTerm.fst
	$(FSTARBOOT) $^ --extract_module FStar.TypeChecker.TcTerm

u_extract_tcinductive: u_boot_fsts/FStar.TypeChecker.TcInductive.fst
	$(FSTARBOOT) $^ --extract_module FStar.TypeChecker.TcInductive

u_extract_tc: u_boot_fsts/FStar.TypeChecker.Tc.fst
	$(FSTARBOOT) $^ --extract_module FStar.TypeChecker.Tc

u_extract_typechecker: u_extract_normalizer u_extract_rel u_extract_util u_extract_dmff u_extract_tcterm u_extract_tcinductive u_extract_tc

u_extract_tosyntax:$(addprefix u_boot_fsts/FStar.ToSyntax., Env.fst ToSyntax.fst)
	$(FSTARBOOT) $^ --extract_namespace FStar.ToSyntax

u_extract_extraction:$(addprefix u_boot_fsts/FStar.Extraction., ML.Syntax.fst ML.UEnv.fst ML.Util.fst ML.Code.fst ML.Term.fst ML.Modul.fst Kremlin.fst)
	$(FSTARBOOT) $^ --extract_namespace FStar.Extraction

u_extract_tactics:$(addprefix u_boot_fsts/FStar.Tactics., Basic.fst Embedding.fst Interpreter.fst)
	# cp tactics/FStar.Tactics.Basic.fs u_boot_fsts/FStar.Tactics.Basic.fst
	# cp tactics/FStar.Tactics.Embedding.fs u_boot_fsts/FStar.Tactics.Embedding.fst
	# cp tactics/FStar.Tactics.Interpreter.fs u_boot_fsts/FStar.Tactics.Interpreter.fst
	$(FSTARBOOT) $^ --extract_namespace FStar.Tactics

u_extract_smtencoding_base: $(addprefix u_boot_fsts/FStar.SMTEncoding., Term.fst Util.fst Z3.fst SplitQueryCases.fst ErrorReporting.fst)
	$(FSTARBOOT) $^ --extract_namespace FStar.SMTEncoding
u_extract_uz: $(addprefix u_boot_fsts/FStar.SMTEncoding., Util.fst Z3.fst)
	$(FSTARBOOT) $^ --extract_namespace FStar.SMTEncoding


u_extract_encode: u_boot_fsts/FStar.SMTEncoding.Encode.fst
	$(FSTARBOOT) $^ --extract_module FStar.SMTEncoding.Encode

u_extract_solver: u_boot_fsts/FStar.SMTEncoding.Solver.fst
	$(FSTARBOOT) $^ --extract_module FStar.SMTEncoding.Solver

u_extract_smtencoding: u_extract_smtencoding_base u_extract_encode u_extract_solver

u_extract_fstar: $(addprefix u_boot_fsts/FStar., Dependencies.fst Interactive.fst Universal.fst Indent.fst Main.fst)
	$(FSTARBOOT) $^ --extract_module FStar.Dependencies --extract_module FStar.Interactive --extract_module FStar.Universal --extract_module FStar.Indent --extract_module FStar.Main

u_extract_all: u_extract_misc u_extract_syntax u_extract_parser	u_extract_typechecker u_extract_tosyntax u_extract_smtencoding u_extract_extraction u_extract_tactics u_extract_fstar

uz:
	make prep
	+make u_extract_uz
	cp u_ocaml-output/*.ml ocaml-output/
	+make -C ocaml-output

ocaml: clean_u_extract_ocaml
	make prep
	+make u_extract_all
	cp u_ocaml-output/*.ml ocaml-output/

# Fastest way to refresh the snapshot (if it works)
ocaml-fstar-ocaml:
	+make boot-ocaml
	+make ocaml
	+make -C ocaml-output

fstar-ocaml:
	+make ocaml
	+make boot-ocaml

boot-ocaml:
	+make -C ocaml-output all

# --------------------------------------------------------------------
# Testing
# --------------------------------------------------------------------

utest:
	make all
ifeq ($(OS),Windows_NT)
	make fsharp-regressions #normalizer failures on linux so only run on windows
endif
	+make -C ocaml-output
	+make fstar-ocaml
	+make uregressions interactive-test

# Interactive mode regressions
interactive-test:
	+make -C tests/interactive

# The regressions to be run with a working F# build of F*
fsharp-regressions:
	$(RUNTIME) $(BIN)/tests.exe

# Getting parallelism from this target
uregressions: ulib uexamples

ulib:
	+make -C ../ulib

uexamples:
	+make -C ../examples all

ulong:
	+make utest
	+make -C ../examples/low-level/crypto extra

wc-boot:
	wc -l $(BOOT_ALL)

ctags:
	ctags --exclude=boot_fsts --exclude=boot_fstis --exclude=ocaml-output -R .
