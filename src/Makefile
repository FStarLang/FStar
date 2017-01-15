# -*- Makefile -*-

# --------------------------------------------------------------------
LIB=../lib
BIN=../bin
ULIB=../ulib

# --------------------------------------------------------------------
# Configuration of some platform-specific tools; eventually we will want a configure script

ifeq ($(OS),Windows_NT)
  FSC     = fsc
  MSBUILD = $(shell cygpath -u \"$$(reg.exe query 'HKLM\SOFTWARE\Microsoft\MSBuild\ToolsVersions\14.0' /v MSBuildToolsPath | tail -n 2 | head -n 1 | sed 's/.*REG_SZ\s\+//g')\")/MSBuild.exe
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

wc: $(BASIC_SRC) $(ABSYN_SRC) $(PARSER_NOGEN_SRC) $(TC_SRC) $(TOSMT_SRC) $(FORMAT_SRC) $(EXTRACTION_SRC) fstar/fstar.fs
	sloccount $^

# --------------------------------------------------------------------
# Bootstrapping in OCaml
# --------------------------------------------------------------------

# JP: these modules are meant to be fsti's (realized in ML); but, the compiler
# currently works in non-universes mode so this is not possible. These files are
# in ulib/ as fstis, though, so the --no_extract argument will go away once the
# F* compiler bootstraps in universes.
NUM=FStar.Int8 FStar.UInt8 FStar.Int16 FStar.UInt16 FStar.Int32 FStar.UInt32 FStar.Int64 FStar.UInt64

# Modules already written as valid .fst files
STDLIB=$(addprefix $(LIB)/, allboot.fsti stboot.fsti list.fsti option.fsti \
  FStar.Float.fsti FStar.Char.fsti $(addsuffix .fst,$(NUM)) FStar.BaseTypes.fsti \
  FStar.Util.fsti FStar.GetOpt.fsti FStar.Unionfind.fsti)
BOOT_BASIC_FSTI=$(addprefix boot_fstis/, string.fsti bytes.fsti platform.fsti version.fsti range.fsti)
BOOT_PRETTYPRINT_FSTI=$(addprefix boot_fstis/, FStar.Pprint.fsti)

# All the .fs and .fsi files that need to be pre-processed into valid .fst files.
BOOT_BASIC_FS=$(addprefix basic/, FStar.Options.fs FStar.Ident.fs FStar.Errors.fs FStar.Const.fs)
BOOT_FORMAT=$(addprefix format/, FStar.Format.fs)
ABSYN=FStar.Absyn.Syntax.fs FStar.Absyn.Const.fs FStar.Absyn.Visit.fs FStar.Absyn.Util.fs FStar.Absyn.Print.fs
ABSYN_SRC=$(addprefix absyn/, $(ABSYN))
SYNTAX=FStar.Syntax.Syntax.fsi FStar.Syntax.Syntax.fs FStar.Syntax.Const.fs FStar.Syntax.Subst.fsi FStar.Syntax.Subst.fs FStar.Syntax.Free.fsi FStar.Syntax.Free.fs \
       FStar.Syntax.InstFV.fsi FStar.Syntax.InstFV.fs FStar.Syntax.Util.fs FStar.Syntax.Print.fsi FStar.Syntax.Print.fs FStar.Syntax.MutRecTy.fsi FStar.Syntax.MutRecTy.fs
SYNTAX_SRC=$(addprefix syntax/, $(SYNTAX))
TC=FStar.Tc.Env.fsi FStar.Tc.Env.fs FStar.Tc.Recheck.fs FStar.Tc.Normalize.fsi FStar.Tc.Normalize.fs FStar.Tc.Errors.fs FStar.Tc.Rel.fsi FStar.Tc.Rel.fs FStar.Tc.Util.fsi FStar.Tc.Util.fs FStar.Tc.Tc.fs
TC_SRC=$(addprefix tc/, $(TC))
TOSMT=FStar.ToSMT.Term.fsi FStar.ToSMT.Term.fs FStar.ToSMT.Z3.fs FStar.ToSMT.SplitQueryCases.fs FStar.ToSMT.Encode.fs
TOSMT_SRC=$(addprefix tosmt/, $(TOSMT))
BOOT_PARSER=$(addprefix parser/, FStar.Parser.ast.fs FStar.Parser.Interleave.fs FStar.Parser.Lexhelp.fs parseit.fsi FStar.Parser.Driver.fs FStar.Parser.Dep.fs FStar.Parser.ToDocument.fs)
DESUGAR_SRC=$(addprefix desugar/, FStar.Parser.DesugarEnv.fs FStar.Parser.Desugar.fs)
TOSYNTAX_SRC=$(addprefix tosyntax/, FStar.ToSyntax.Env.fsi FStar.ToSyntax.Env.fs FStar.ToSyntax.ToSyntax.fsi FStar.ToSyntax.ToSyntax.fs)
TYPECHECKER=$(addprefix FStar.TypeChecker., Common.fs Env.fsi Env.fs Normalize.fsi Normalize.fs Err.fs Rel.fsi Rel.fs Util.fsi Util.fs DMFF.fsi DMFF.fs TcTerm.fsi TcTerm.fs Tc.fsi Tc.fs)
TYPECHECKER_SRC=$(addprefix typechecker/, $(TYPECHECKER))
EXTRACTION=$(addprefix FStar.Extraction., ML.Syntax.fs ML.UEnv.fs ML.Util.fs ML.Code.fsi ML.Code.fs ML.Term.fs ML.Modul.fs kremlin.fs)
EXTRACTION_SRC=$(addprefix extraction/, $(EXTRACTION))
STRATIFIEDEXTRACTION_SRC=$(addprefix stratifiedextraction/FStar.StratifiedExtraction.ML., Env.fs Util.fs ExtractTyp.fs ExtractExp.fs ExtractMod.fs)
FSDOC=FStar.Fsdoc.Generator.fs
FSDOC_SRC=$(addprefix fsdoc/, $(FSDOC))
SMTENCODING=$(addprefix FStar.SMTEncoding., Term.fsi Term.fs Util.fs Z3.fs SplitQueryCases.fs ErrorReporting.fsi ErrorReporting.fs Encode.fsi Encode.fs Solver.fsi Solver.fs)
SMTENCODING_SRC=$(addprefix smtencoding/, $(SMTENCODING))
TOPLEVEL=$(addprefix FStar., Dependencies.fs Interactive.fs Stratified.fs Universal.fs Indent.fs FStar.fs)
TOPLEVEL_SRC=$(addprefix fstar/, $(TOPLEVEL))

BOOT_ALL=$(BOOT_BASIC_FS) $(BOOT_FORMAT) $(ABSYN_SRC) $(SYNTAX_SRC) $(TC_SRC) \
  $(TOSMT_SRC) $(BOOT_PARSER) $(DESUGAR_SRC) $(TOSYNTAX_SRC) $(TYPECHECKER_SRC) \
  $(EXTRACTION_SRC) $(STRATIFIEDEXTRACTION_SRC) $(FSDOC_SRC) $(SMTENCODING_SRC) $(TOPLEVEL_SRC)

ALL_INTERFACES=$(STDLIB) $(BOOT_BASIC_FSTI) $(BOOT_PRETTYPRINT_FSTI)
# In the dependency order... eventually we want to use auto-deps
ALL_SOURCES=FStar.Options.fst FStar.Ident.fst FStar.Const.fst FStar.Errors.fst \
	        FStar.Format.fst \
	    	FStar.Absyn.Syntax.fst FStar.Absyn.Const.fst FStar.Absyn.Visit.fst FStar.Absyn.Util.fst FStar.Absyn.Print.fst \
	    	FStar.Syntax.Syntax.fst FStar.Syntax.Const.fst FStar.Syntax.Subst.fst FStar.Syntax.Free.fst FStar.Syntax.InstFV.fst FStar.Syntax.Util.fst FStar.Syntax.Print.fst \
		FStar.Syntax.MutRecTy.fst \
	    	FStar.Tc.Env.fst FStar.Tc.Recheck.fst FStar.Tc.Normalize.fst FStar.Tc.Errors.fst FStar.Tc.Rel.fst FStar.Tc.Util.fst FStar.Tc.Tc.fst \
	    	FStar.ToSMT.Term.fst FStar.ToSMT.Z3.fst FStar.ToSMT.SplitQueryCases.fst FStar.ToSMT.Encode.fst \
	    	FStar.TypeChecker.Common.fst FStar.TypeChecker.Env.fst FStar.TypeChecker.Normalize.fst FStar.TypeChecker.Err.fst FStar.TypeChecker.Rel.fst FStar.TypeChecker.Util.fst FStar.TypeChecker.DMFF.fst FStar.TypeChecker.TcTerm.fst FStar.TypeChecker.Tc.fst \
		FStar.Parser.AST.fst FStar.Parser.Interleave.fst FStar.Parser.ToDocument.fst FStar.Parser.Parse.fsti FStar.Parser.Lexhelp.fst FStar.Parser.ParseIt.fsti FStar.Parser.Driver.fst FStar.Parser.Dep.fst \
		FStar.Parser.DesugarEnv.fst FStar.Parser.Desugar.fst \
		FStar.ToSyntax.Env.fst FStar.ToSyntax.ToSyntax.fst \
		FStar.Extraction.ML.Syntax.fst FStar.Extraction.ML.UEnv.fst FStar.Extraction.ML.Util.fst FStar.Extraction.ML.Code.fst FStar.Extraction.ML.Term.fst FStar.Extraction.ML.Modul.fst FStar.Extraction.Kremlin.fst \
		FStar.StratifiedExtraction.ML.Env.fst FStar.StratifiedExtraction.ML.Util.fst FStar.StratifiedExtraction.ML.ExtractTyp.fst FStar.StratifiedExtraction.ML.ExtractExp.fst FStar.StratifiedExtraction.ML.ExtractMod.fst \
		FStar.Fsdoc.Generator.fst \
	    	FStar.SMTEncoding.Term.fst FStar.SMTEncoding.Util.fst FStar.SMTEncoding.Z3.fst FStar.SMTEncoding.SplitQueryCases.fst FStar.SMTEncoding.ErrorReporting.fst FStar.SMTEncoding.Encode.fst FStar.SMTEncoding.Solver.fst \
	    	FStar.Dependencies.fst FStar.Interactive.fst FStar.Stratified.fst FStar.Universal.fst FStar.Indent.fst FStar.FStar.fst

ADMITTED_MODULES=System System.IO System.Text System.Diagnostics System.Collections.Generic Collections FStar.Heap FStar.ST FStar.All FStar.List FStar.Option FStar.Char FStar.String FStar.List FStar.Bytes FStar.Platform FStar.Util FStar.Version FStar.Getopt FStar.Range FStar.Unionfind FStar.Parser.ParseIt FStar.Parser.Parse FStar.Pprint
ADMITS=$(addprefix --admit_fsi , $(ADMITTED_MODULES))

FSTAROPTS=

all_boot_fsts:
	./tools/make_all_boot_fsts "$(BOOT_ALL)"


# SI: does it have to go prettyprint.fsti->FStar.Pprint.fsti?
boot_fstis/FStar.Pprint.fsti: prettyprint/prettyprint.fsi
	cp $^ $@

boot_fstis/%.fsti: basic/%.fsi
	cp $^ $@

boot_fsts/FStar.Parser.Parse.fsti: parser/parse.fsi
	$(HEAD) -n -12 $^ > $@
	$(SED) -i 's/module FStar.Parser.Parse/module FStar.Parser.Parse open FStar.BaseTypes type bytes = array<byte>/' $@

boot_fsts/FStar.Parser.ParseIt.fsti: parser/parseit.fsi
	cp $^ $@

# TODO: files generated by the build system should not go into $(LIB)
$(LIB)/FStar.Util.fsti: basic/util.fsi
	cat $^ | $(SED) 's/open System.IO//g' | $(SED) 's/type time.*/new type time/g' | $(SED) 's/type smap.*/new type smap : Type -> Type/g' | $(SED) 's/type out_channel.*/new type out_channel/g' | $(SED) 's/type file_handle.*/new type file_handle/g' | $(SED) 's/type stream_reader.*/new type stream_reader/g' | $(SED) 's/type string_builder.*/new type string_builder/g' | $(SED) 's/type proc.*/new type proc/g' | $(SED) 's/type set.*/new type set:Type -> Type/g' > $@

$(LIB)/FStar.GetOpt.fsti: basic/getopt.fsi
	cp $^ $@

$(LIB)/FStar.Unionfind.fsti: basic/unionfind.fsi
	cat $^ | $(SED) 's/type cell.*//g' | $(SED) 's/and contents.*//g' | $(SED) 's/.*| Data.*//g' | $(SED) 's/.*| Fwd.*//g' | $(SED) 's/type uvar.*/new type uvar : Type -> Type/g' > $@

clean_ocaml_prep:
	rm -rf boot_fsts boot_fstis
	mkdir boot_fsts boot_fstis
	cp basic/bytes.fsti boot_fstis/

extract_ocaml_prep: all_boot_fsts

extract_ocaml: $(ALL_INTERFACES) $(addprefix boot_fsts/, $(ALL_SOURCES))
	$(FSTAR) --stratified --explicit_deps --eager_inference \
	  --lax --fs_typ_app --no_location_info $(addprefix --no_extract \
	  ,$(NUM)) --odir ocaml-output --MLish $(FSTAROPTS) --codegen OCaml $^

U_STDLIB=$(addprefix $(ULIB)/, FStar.FunctionalExtensionality.fst FStar.PropositionalExtensionality.fst FStar.PredicateExtensionality.fst \
			       FStar.TSet.fst FStar.Set.fst \
			       FStar.Heap.fst FStar.ST.fst FStar.All.fst \
			       FStar.Char.fsti FStar.Float.fsti FStar.Mul.fst FStar.Int.fst $(addsuffix .fst,$(NUM)) FStar.BaseTypes.fsti)
U_BOOT_BASIC_FSTI=$(addprefix boot_fstis/FStar., string.fsti list.fst util.fsti platform.fsti bytes.fst range.fsti version.fsti getopt.fsti unionfind.fsti Pprint.fsti)
U_ALL_INTERFACES=$(U_STDLIB) $(U_BOOT_BASIC_FSTI) boot_fstis/FStar.Parser.Parse.fsti

boot_fstis/FStar.%.fsti: basic/%.fsi
	cp $^ $@

boot_fstis/FStar.list.fst: basic/list.fsi
	cp $^ $@
	$(SED) -i 's/open Prims/module ALL_TEMP = FStar.All/g' $@
	$(SED) -i 's/<.* when .* : equality>//g' $@
	$(SED) -i 's/val/assume val/g' $@

boot_fstis/FStar.bytes.fst: basic/bytes.fsti
	cp $^ $@
	$(SED) -i 's/val/assume val/g' $@
	$(SED) -i 's/new/assume new/g' $@

boot_fstis/FStar.util.fsti: basic/util.fsi
	cp $^ $@
	$(SED) -i 's/open System.IO/module ALL_TMP = FStar.All/g' $@
	$(SED) -i 's/type time.*/assume new type time/g'  $@ 
	$(SED) -i 's/type smap.*/assume new type smap : Type0 -> Type0/g'  $@ 
	$(SED) -i 's/type out_channel.*/assume new type out_channel/g'  $@ 
	$(SED) -i 's/type file_handle.*/assume new type file_handle/g'  $@ 
	$(SED) -i 's/type stream_reader.*/assume new type stream_reader/g'  $@ 
	$(SED) -i 's/type string_builder.*/assume new type string_builder/g'  $@ 
	$(SED) -i 's/type proc.*/assume new type proc/g' $@ 
	$(SED) -i 's/type set.*/assume new type set:Type0 -> Type0/g' $@

boot_fstis/FStar.unionfind.fsti: basic/unionfind.fsi
	cp $^ $@
	$(SED) -i 's/type cell.*/module ALL_TMP = FStar.All/g' $@
	$(SED) -i 's/and contents.*//g' $@
	$(SED) -i 's/.*| Data.*//g' $@
	$(SED) -i 's/.*| Fwd.*//g' $@
	$(SED) -i 's/type uvar.*/assume new type uvar : Type0 -> Type0/g' $@

boot_fstis/FStar.Parser.Parse.fsti: parser/parse.fsi
	$(HEAD) -n -12 $^ > $@
	$(SED) -i 's/module FStar.Parser.Parse/module FStar.Parser.Parse open FStar.BaseTypes type bytes = array<byte>/' $@

U_TOPLEVEL_SRC=$(addprefix fstar/FStar., Dependencies.fs Interactive.fs Universal.fs Indent.fs) #Stratified.fs  FStar.fs)

U_BOOT_ALL=$(BOOT_BASIC_FS) $(BOOT_FORMAT) $(SYNTAX_SRC) \
	   $(BOOT_PARSER) $(TOSYNTAX_SRC) $(TYPECHECKER_SRC) \
	   $(EXTRACTION_SRC) $(SMTENCODING_SRC) $(FSDOC_SRC) $(U_TOPLEVEL_SRC)

rename_as_fst:
	./tools/rename_all_boot_fsts "$(U_BOOT_ALL)"
	mv u_boot_fsts/parseit.fsti u_boot_fsts/FStar.Parser.ParseIt.fsti

prep_u_extract_ocaml: $(U_ALL_INTERFACES)
	make rename_as_fst
	$(SED) -i "s/type term' =/type term' : Type0 =/g"      u_boot_fsts/FStar.Syntax.Syntax.fst* #TODO, fix up universe generalization for mutual recursive types, issue #806
	$(SED) -i "s/and pat' =/and pat' : Type0 =/g"          u_boot_fsts/FStar.Syntax.Syntax.fst* #TODO, fix up universe generalization for mutual recursive types, issue #806
	$(SED) -i "s/and comp' =/and comp' : Type0 =/g"        u_boot_fsts/FStar.Syntax.Syntax.fst* #TODO, fix up universe generalization for mutual recursive types, issue #806
	$(SED) -i 's/type env =/type env : Type0 =/g'          u_boot_fsts/FStar.TypeChecker.Env.fst* #TODO, fix up universe generalization for mutual recursive types, issue #806
	$(SED) -i 's/and solver_t =/and solver_t : Type0 =/g'  u_boot_fsts/FStar.TypeChecker.Env.fst* #TODO, fix up universe generalization for mutual recursive types, issue #806
	$(SED) -i 's/and guard_t =/and guard_t : Type0 =/g'    u_boot_fsts/FStar.TypeChecker.Env.fst* #TODO, fix up universe generalization for mutual recursive types, issue #806
	$(SED) -i "s/type term' =/type term': Type0 =/g"       u_boot_fsts/FStar.SMTEncoding.Term.fst* #TODO, fix up universe generalization for mutual recursive types, issue #806
	$(SED) -i "s/type term' =/type term': Type0 =/g"       u_boot_fsts/FStar.SMTEncoding.Term.fst* #TODO, fix up universe generalization for mutual recursive types, issue #806
	$(SED) -i "s/type term' =/type term': Type0 =/g"       u_boot_fsts/FStar.Parser.AST.fst #TODO, fix up universe generalization for mutual recursive types, issue #806
	$(SED) -i "s/type pattern' =/type pattern': Type0 =/g" u_boot_fsts/FStar.Parser.AST.fst #TODO, fix up universe generalization for mutual recursive types, issue #806
	$(SED) -i "s/type decl' =/type decl': Type0 =/g"       u_boot_fsts/FStar.Parser.AST.fst #TODO, fix up universe generalization for mutual recursive types, issue #806
	$(SED) -i "s/type mlexpr' =/type mlexpr': Type0 =/g"   u_boot_fsts/FStar.Extraction.ML.Syntax.fst #TODO, fix up universe generalization for mutual recursive types, issue #806
	$(SED) -i "s/type mlsig1 =/type mlsig1: Type0 =/g"     u_boot_fsts/FStar.Extraction.ML.Syntax.fst #TODO, fix up universe generalization for mutual recursive types, issue #806
	$(SED) -i 's/module FStar.Parser.Lexhelp/module FStar.Parser.Lexhelp open FStar.Mul/' u_boot_fsts/FStar.Parser.Lexhelp.fst #uses * for multiplication only

clean_u_extract_ocaml:
	rm -rf boot_fstis u_boot_fsts u_ocaml-output
	mkdir boot_fstis u_boot_fsts u_ocaml-output
	make prep_u_extract_ocaml

NOEXTRACT=$(NUM) \
FStar.UInt \
FStar.Int \
FStar.Mul \
FStar.StrongExcludedMiddle \
FStar.List.Tot \
FStar.Classical \
FStar.ListProperties \
FStar.Seq \
FStar.SeqProperties \
FStar.Math.Lib \
FStar.Math.Lemmas \
FStar.BitVector \
FStar.FunctionalExtensionality \
FStar.PropositionalExtensionality \
FStar.PredicateExtensionality \
FStar.TSet \
FStar.Heap \
FStar.ST \
FStar.All \
FStar.List

FSTARBOOT=$(FSTAR) $(OTHERFLAGS) --eager_inference --MLish --lax --fs_typ_app --no_location_info \
		   --odir u_ocaml-output --codegen OCaml --include ../ulib --include u_boot_fsts --include boot_fstis

u_extract_misc:$(addprefix u_boot_fsts/, FStar.Options.fst FStar.Ident.fst FStar.Errors.fst FStar.Const.fst \
					 FStar.Format.fst)
	$(FSTARBOOT) $^ $(addprefix --extract_module , FStar.Options FStar.Ident FStar.Errors FStar.Const FStar.Format)

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

u_extract_tc: u_boot_fsts/FStar.TypeChecker.Tc.fst
	$(FSTARBOOT) $^ --extract_module FStar.TypeChecker.Tc

u_extract_typechecker: u_extract_normalizer u_extract_rel u_extract_util u_extract_dmff u_extract_tcterm u_extract_tc 

u_extract_tosyntax:$(addprefix u_boot_fsts/FStar.ToSyntax., Env.fst ToSyntax.fst)
	$(FSTARBOOT) $^ --extract_namespace FStar.ToSyntax

u_extract_extraction:$(addprefix u_boot_fsts/FStar.Extraction., ML.Syntax.fst ML.UEnv.fst ML.Util.fst ML.Code.fst ML.Term.fst ML.Modul.fst Kremlin.fst)
	$(FSTARBOOT) $^ --extract_namespace FStar.Extraction

u_extract_smtencoding_base: $(addprefix u_boot_fsts/FStar.SMTEncoding., Term.fst Util.fst Z3.fst SplitQueryCases.fst ErrorReporting.fst)
	$(FSTARBOOT) $^ --extract_namespace FStar.SMTEncoding

u_extract_encode: u_boot_fsts/FStar.SMTEncoding.Encode.fst
	$(FSTARBOOT) $^ --extract_module FStar.SMTEncoding.Encode

u_extract_solver: u_boot_fsts/FStar.SMTEncoding.Solver.fst
	$(FSTARBOOT) $^ --extract_module FStar.SMTEncoding.Solver

u_extract_smtencoding: u_extract_encode u_extract_solver

u_extract_fstar: $(addprefix u_boot_fsts/FStar., Dependencies.fst Interactive.fst Universal.fst Indent.fst) #Stratified.fs  FStar.fs)
	$(FSTARBOOT) $^ --extract_module FStar.Dependencies --extract_module FStar.Interactive --extract_module FStar.Universal --extract_module FStar.Indent

u_extract_all: u_extract_misc u_extract_syntax u_extract_parser \
	       u_extract_typechecker u_extract_tosyntax u_extract_smtencoding \
	       u_extract_extraction #u_extract_fstar

u_ocaml: clean_u_extract_ocaml
	+make u_extract_misc u_extract_syntax u_extract_parser \
              u_extract_typechecker u_extract_tosyntax u_extract_smtencoding \
	      u_extract_extraction u_extract_fstar
	cp u_ocaml-output/*.ml ocaml_output/

# Fastest way to refresh the snapshot (if it works)
ocaml-fstar-ocaml:
	+make boot-ocaml
	+make ocaml
	+make -C ocaml-output

fstar-ocaml:
	+make ocaml
	+make boot-ocaml

ocaml:
	+make clean_ocaml_prep
	+make extract_ocaml_prep
	+make extract_ocaml

boot-ocaml:
	# +make -C ocaml-output clean
	+make -C ocaml-output all

# --------------------------------------------------------------------
# Bootstrapping in F#
# --------------------------------------------------------------------

BASELIBS    = $(addprefix -r , $(FSHARP_LIBS) $(OTHER_DLLS))
FS_SUPPORT_LIBS=native_int/prims.fs st.fs all.fs option.fs
FSTAR_SUPPORT_LIBS=char.fsi char.fs string.fsi string.fs list.fsi list.fs util.fsi util.fs platform.fsi platform.fs bytes.fsi bytes.fs range.fsi range.fs getopt.fsi getopt.fs version.fsi version.fs unionfind.fsi unionfind.fs
BOOT_FS_BASE=FStar.Options.fs
BOOT_FS_SYNTAX=FStar.Absyn.Syntax.fs FStar.Absyn.Const.fs FStar.Absyn.Visit.fs FStar.Absyn.Util.fs FStar.Absyn.Print.fs
BOOT_FS_TC=FStar.Tc.Env.fs FStar.Tc.Recheck.fs FStar.Tc.Normalize.fs FStar.Tc.Errors.fs FStar.Tc.Rel.fs FStar.Tc.Util.fs FStar.Tc.Tc.fs
BOOT_FS_PARSER=FStar.Parser.AST.fs parseutil.fs parse.fs FStar.Parser.Lexhelp.fs lex.fs FStar.Parser.DesugarEnv.fs FStar.Parser.Desugar.fs parseit.fs FStar.Parser.Driver.fs
BOOT_FS_FORMAT=FSharp.Format.fs # FSharp? you mean FStar?
BOOT_FS_PRETTYPRINT=FSharp.PPrint.fs
BOOT_FS_TOSMT=FStar.ToSMT.Term.fs FStar.ToSMT.Z3.fs FStar.ToSMT.SplitQueryCases.fs FStar.ToSMT.Encode.fs
BOOT_FS_EXTRACTION=FStar.Extraction.ML.Syntax.fs FStar.Extraction.ML.Env.fs FStar.Extraction.ML.Util.fs FStar.Extraction.ML.Code.fs FStar.Extraction.ML.ExtractTyp.fs FStar.Extraction.ML.ExtractExp.fs FStar.Extraction.ML.ExtractMod.fs FStar.Extraction.Kremlin.fs
BOOT_FS_FSDOC=FStar.Fsdoc.Generator.fs
BOOT_FS_FILES=$(BOOT_FS_BASE) $(BOOT_FS_SYNTAX) $(BOOT_FS_TC) $(BOOT_FS_PARSER) $(BOOT_FS_FORMAT) $(BOOT_FS_PRETTYPRINT) $(BOOT_FS_TOSMT) $(BOOT_FS_EXTRACTION) $(BOOT_FS_FSDOC) FStar.FStar.fs

boot-fsharp: fsharp-output fs plain-fs-files fsharp-output/fstar.exe

fsharp-output/fstar.exe: $(addprefix ../lib/fs/, $(FS_SUPPORT_LIBS)) $(addprefix basic/, $(FSTAR_SUPPORT_LIBS)) $(addprefix fsharp-output/, $(BOOT_FS_FILES) main.fs)
	$(FSC) --nowarn:0025 -o $@ $(BASELIBS) $(FSCOTHERFLAGS) $^

fs: $(BOOT_ALL)
	$(FSTAR) --explicit_deps --eager_inference --MLish --lax --fs_typ_app \
	  --odir fsharp-output $(FSTAROPTS) --codegen FSharp $(ADMITS) $^

fsharp-output: nuget-restore
	mkdir -p fsharp-output
	cp ../bin/FSharp.PowerPack.* fsharp-output

plain-fs-files: $(addprefix parser/, parseutil.fs parse.fs lex.fs parseit.fs) fstar/main.fs
	cp $^ fsharp-output/

deploy-boot-fs: fsharp-output/fstar.exe
	cp $^ ../bin
	cp $^ ../bin/fstar.fsharp

clean-boot-fs:
	rm -rf fsharp-output

# --------------------------------------------------------------------
# Testing
# --------------------------------------------------------------------

test:
	make all
	make fsharp-regressions
	make fstar-ocaml
	make regressions

utest:
	make all
	make fsharp-regressions
	+make -C ocaml-output
	+make fstar-ocaml
	+make uregressions

# The regressions to be run with a working F# build of F*
fsharp-regressions:
	$(RUNTIME) $(BIN)/tests.exe

# The regressions to be run with a working OCaml build of F*
regressions:
	make -C ../lib
	+make -C ../ulib
	+make -C ../examples
	make -C ../examples/hello ocaml
	make -C ../ucontrib/CoreCrypto/ml/ test
	make -C ../examples/crypto clean #rpc-test cnt-test #removed until we can add it in uregressions
	#make -C ../examples/wysteria a.out distclean

# Getting parallelism from this target
uregressions: ulib uexamples

ulib:
	+make -C ../ulib

uexamples:
	+make -C ../examples uall

examples:
	+make -C ../examples sall

ulong:
	+make utest
	+make -C ../examples/low-level/crypto extra

wc-boot:
	wc -l $(BOOT_ALL)

ctags:
	ctags --exclude=boot_fsts --exclude=boot_fstis --exclude=ocaml-output -R .
