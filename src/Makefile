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

# --------------------------------------------------------------------
# Bootstrapping in OCaml
# --------------------------------------------------------------------

# This is the way in which we invoke F* for boostrapping
#   -- we use automatic dependence analysis based on files in ulib, src/{basic, ...} and boot
#   -- eager_inference, MLish, lax: all tune type-inference for use with unverified ML programs
FSTARBOOT=$(FSTAR) $(OTHERFLAGS) --eager_inference --lax --MLish --no_location_info \
		   --odir ocaml-output --codegen OCaml \
			$(addprefix --include , ../ulib boot basic extraction format fsdoc fstar \
                                    parser prettyprint reflection smtencoding syntax \
                                    tactics tosyntax typechecker)

ALL_BOOT=$(addprefix boot/FStar., \
           Util.fsti List.fsti Bytes.fsti String.fsti \
		   Pprint.fsti Parser.Parse.fsti \
		   Tactics.Interpreter.fst Tactics.Interpreter.fsti)

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

boot/FStar.Parser.Parse.fsti: parser/boot/parse.fsi | boot_dir
	echo "#light \"off\"" > $@
	$(HEAD) -n -12 $^ >> $@
	$(SED) -i 's/module FStar.Parser.Parse/module FStar.Parser.Parse\nopen FStar.All\nopen FStar.BaseTypes\ntype bytes = array<byte>\nopen FStar.Syntax.Syntax/' $@

boot/%.fst: basic/boot/%.fs | boot_dir
	cp $^ $@

boot/FStar.Parser.Parse.fst: parser/boot/parse.fs | boot_dir
	cp $^ $@

boot/FStar.Tactics.Interpreter.fsti: tactics/boot/FStar.Tactics.Interpreter.fsi | boot_dir
	cp $^ $@

boot_dir:
	mkdir -p boot

boot: $(ALL_BOOT)

clean_boot:
	rm -rf boot

MISC_EXTRACTED_FILES=$(addprefix basic/, FStar.Common.fs FStar.Ident.fs FStar.Options.fs FStar.Range.fs FStar.Errors.fs FStar.Const.fs FStar.Order.fs) format/FStar.Format.fs
extract_misc: boot $(MISC_EXTRACTED_FILES)
	$(FSTARBOOT) $(MISC_EXTRACTED_FILES) $(addprefix --extract_module , FStar.Pervasives FStar.Common FStar.Range FStar.Options FStar.Ident FStar.Errors FStar.Const FStar.Format FStar.Order)

SYNTAX_EXTRACTED_FILES=$(addprefix syntax/FStar.Syntax., Syntax.fs Subst.fs Free.fs InstFV.fs Util.fs Print.fs Embeddings.fs MutRecTy.fs Resugar.fs Unionfind.fs) fsdoc/FStar.Fsdoc.Generator.fs
extract_syntax: boot $(SYNTAX_EXTRACTED_FILES)
	$(FSTARBOOT) $(SYNTAX_EXTRACTED_FILES) --extract_namespace FStar.Syntax --extract_namespace FStar.Fsdoc

PARSER_EXTRACTED_FILES=$(addprefix parser/FStar.Parser., AST.fs ParseIt.fsi Driver.fs Dep.fs ToDocument.fs)
extract_parser: boot $(PARSER_EXTRACTED_FILES)
	$(FSTARBOOT) $(PARSER_EXTRACTED_FILES) --extract_namespace FStar.Parser

NORMALIZER_EXTRACTED_FILES=$(addprefix typechecker/FStar.TypeChecker., Common.fs Env.fs Normalize.fs Err.fs)
extract_normalizer: boot $(NORMALIZER_EXTRACTED_FILES)
	$(FSTARBOOT) $(NORMALIZER_EXTRACTED_FILES) --extract_namespace FStar.TypeChecker

REL_EXTRACTED_FILES=typechecker/FStar.TypeChecker.Rel.fs
extract_rel: boot $(REL_EXTRACTED_FILES)
	$(FSTARBOOT) $(REL_EXTRACTED_FILES) --extract_module FStar.TypeChecker.Rel

UTIL_EXTRACTED_FILES=typechecker/FStar.TypeChecker.Util.fs
extract_util: boot $(UTIL_EXTRACTED_FILES)
	$(FSTARBOOT) $(UTIL_EXTRACTED_FILES) --extract_module FStar.TypeChecker.Util

DMFF_EXTRACTED_FILES=typechecker/FStar.TypeChecker.DMFF.fs
extract_dmff: boot $(DMFF_EXTRACTED_FILES)
	$(FSTARBOOT) $(DMFF_EXTRACTED_FILES) --extract_module FStar.TypeChecker.DMFF

TCTERM_EXTRACTED_FILES=typechecker/FStar.TypeChecker.TcTerm.fs
extract_tcterm: boot $(TCTERM_EXTRACTED_FILES)
	$(FSTARBOOT) $(TCTERM_EXTRACTED_FILES) --extract_module FStar.TypeChecker.TcTerm

TCINDUCTIVE_EXTRACTED_FILES=typechecker/FStar.TypeChecker.TcInductive.fs
extract_tcinductive: boot $(TCINDUCTIVE_EXTRACTED_FILES)
	$(FSTARBOOT) $(TCINDUCTIVE_EXTRACTED_FILES) --extract_module FStar.TypeChecker.TcInductive

TC_EXTRACTED_FILES=typechecker/FStar.TypeChecker.Tc.fs
extract_tc: boot $(TC_EXTRACTED_FILES)
	$(FSTARBOOT) $(TC_EXTRACTED_FILES) --extract_module FStar.TypeChecker.Tc

TOSYNTAX_EXTRACTED_FILES=$(addprefix tosyntax/FStar.ToSyntax., Env.fs Interleave.fs ToSyntax.fs)
extract_tosyntax: boot $(TOSYNTAX_EXTRACTED_FILES)
	$(FSTARBOOT) $(TOSYNTAX_EXTRACTED_FILES) --extract_namespace FStar.ToSyntax

EXTRACTION_EXTRACTED_FILES=$(addprefix extraction/FStar.Extraction., ML.Syntax.fs ML.UEnv.fs ML.Util.fs ML.Code.fs ML.Term.fs ML.Modul.fs Kremlin.fs)
extract_extraction: boot $(EXTRACTION_EXTRACTED_FILES)
	$(FSTARBOOT) $(EXTRACTION_EXTRACTED_FILES) --extract_namespace FStar.Extraction

TACTICS_EXTRACTED_FILES=../ulib/FStar.Tactics.Types.fsti $(addprefix tactics/FStar.Tactics., Types.fs Basic.fs Embedding.fs Native.fs) boot/FStar.Tactics.Interpreter.fst
extract_tactics: boot $(TACTICS_EXTRACTED_FILES)
	$(FSTARBOOT) $(TACTICS_EXTRACTED_FILES) --extract_namespace FStar.Tactics --no_extract FStar.Tactics.Native

REFLECTION_EXTRACTED_FILES=../ulib/FStar.Reflection.Types.fsti $(addprefix reflection/FStar.Reflection., Basic.fs Data.fs Interpreter.fs)
extract_reflection: boot $(REFLECTION_EXTRACTED_FILES)
	$(FSTARBOOT) $(REFLECTION_EXTRACTED_FILES) --extract_namespace FStar.Reflection

SMTENCODING_EXTRACTED_FILES=$(addprefix smtencoding/FStar.SMTEncoding., Term.fs Util.fs Z3.fs SplitQueryCases.fs ErrorReporting.fs)
extract_smtencoding_base: boot $(SMTENCODING_EXTRACTED_FILES)
	$(FSTARBOOT) $(SMTENCODING_EXTRACTED_FILES) --extract_namespace FStar.SMTEncoding

UZ_EXTRACTED_FILES=$(addprefix smtencoding/FStar.SMTEncoding., Util.fs Z3.fs)
extract_uz: boot $(UZ_EXTRACTED_FILES)
	$(FSTARBOOT) $(UZ_EXTRACTED_FILES) --extract_namespace FStar.SMTEncoding

ENCODE_EXTRACTED_FILES=smtencoding/FStar.SMTEncoding.Encode.fs
extract_encode: boot $(ENCODE_EXTRACTED_FILES)
	$(FSTARBOOT) $(ENCODE_EXTRACTED_FILES) --extract_module FStar.SMTEncoding.Encode

SOLVER_EXTRACTED_FILES=smtencoding/FStar.SMTEncoding.Solver.fs
extract_solver: boot $(SOLVER_EXTRACTED_FILES)
	$(FSTARBOOT) $(SOLVER_EXTRACTED_FILES) --extract_module FStar.SMTEncoding.Solver

FSTAR_EXTRACTED_FILES=$(addprefix fstar/FStar., Dependencies.fs Interactive.Legacy.fs Interactive.CompletionTable.fs Interactive.Ide.fs Universal.fs Indent.fs Main.fs)
extract_fstar: boot $(FSTAR_EXTRACTED_FILES)
	$(FSTARBOOT) $(FSTAR_EXTRACTED_FILES) --extract_module FStar.Dependencies --extract_module FStar.Interactive.CompletionTable --extract_module FStar.Interactive.Ide --extract_module FStar.Interactive.Legacy --extract_module FStar.Universal --extract_module FStar.Indent --extract_module FStar.Main

extract_typechecker: extract_normalizer extract_rel extract_util extract_dmff extract_tcterm extract_tcinductive extract_tc

extract_smtencoding: extract_smtencoding_base extract_encode extract_solver

extract_all: extract_tactics extract_reflection extract_misc extract_syntax extract_parser extract_typechecker extract_tosyntax extract_smtencoding extract_extraction extract_fstar

clean_extracted:
	rm -f ocaml-output/FStar_*.ml

ocaml: boot
	+$(MAKE) extract_all

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
uregressions: hello native_tactics ulib tutorial uexamples extraction-examples interactive-test

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
