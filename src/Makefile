# -*- Makefile -*-

# --------------------------------------------------------------------
LIB=../lib
BIN=../bin

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

clean:
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
BOOT_PRETTYPRINT_FSTI=$(addprefix boot_fstis/, prettyprint.fsti)

# All the .fs and .fsi files that need to be pre-processed into valid .fst files.
BOOT_BASIC_FS=$(addprefix basic/, options.fs ident.fs const.fs)
BOOT_FORMAT=$(addprefix format/, formatml.fs)
ABSYN=syntax.fs const.fs visit.fs util.fs print.fs
ABSYN_SRC=$(addprefix absyn/, $(ABSYN))
SYNTAX=syntax.fsi syntax.fs const.fs subst.fsi subst.fs free.fsi free.fs instfv.fsi instfv.fs util.fs print.fsi print.fs
SYNTAX_SRC=$(addprefix syntax/, $(SYNTAX))
TC=tcenv.fsi tcenv.fs recheck.fs normalize.fsi normalize.fs errors.fs rel.fsi rel.fs tcutil.fsi tcutil.fs tc.fs
TC_SRC=$(addprefix tc/, $(TC))
TOSMT=term.fsi term.fs z3.fs splitcases.fs encode.fs
TOSMT_SRC=$(addprefix tosmt/, $(TOSMT))
BOOT_PARSER=$(addprefix parser/, ast.fs dsenv.fs desugar.fs env.fs interleave.fs tosyntax.fs lexhelp.fs parseit.fsi driver.fs dep.fs)
TYPECHECKER=common.fs env.fsi env.fs normalize.fsi normalize.fs errors.fs rel.fsi rel.fs util.fsi util.fs dmff.fs tcterm.fsi tcterm.fs tc.fsi tc.fs
TYPECHECKER_SRC=$(addprefix typechecker/, $(TYPECHECKER))
EXTRACTION=ml-syntax.fs env.fs uenv.fs util.fs codegen.fsi codegen.fs extracttyp.fs extractexp.fs extractmod.fs term.fs modul.fs kremlin.fs
EXTRACTION_SRC=$(addprefix extraction/, $(EXTRACTION))
FSDOC=generator.fs
FSDOC_SRC=$(addprefix fsdoc/, $(FSDOC))
SMTENCODING=term.fsi term.fs util.fs z3.fs splitcases.fs errorReporting.fs encode.fs solver.fs
SMTENCODING_SRC=$(addprefix smtencoding/, $(SMTENCODING))
TOPLEVEL=dependences.fs interactive.fs stratified.fs universal.fs fstar.fs
TOPLEVEL_SRC=$(addprefix fstar/, $(TOPLEVEL))

BOOT_ALL=$(BOOT_BASIC_FS) $(BOOT_FORMAT) $(ABSYN_SRC) $(SYNTAX_SRC) $(TC_SRC) \
  $(TOSMT_SRC) $(BOOT_PARSER) $(TYPECHECKER_SRC) $(EXTRACTION_SRC) $(FSDOC_SRC) $(SMTENCODING_SRC) $(TOPLEVEL_SRC)

ALL_INTERFACES=$(STDLIB) $(BOOT_BASIC_FSTI) $(BOOT_PRETTYPRINT_FSTI)
# In the dependency order... eventually we want to use auto-deps
ALL_SOURCES=FStar.Options.fst FStar.Ident.fst FStar.Const.fst \
	        FStar.Format.fst \
	    	FStar.Absyn.Syntax.fst FStar.Absyn.Const.fst FStar.Absyn.Visit.fst FStar.Absyn.Util.fst FStar.Absyn.Print.fst \
	    	FStar.Syntax.Syntax.fst FStar.Syntax.Const.fst FStar.Syntax.Subst.fst FStar.Syntax.Free.fst FStar.Syntax.InstFV.fst FStar.Syntax.Util.fst FStar.Syntax.Print.fst \
	    	FStar.Tc.Env.fst FStar.Tc.Recheck.fst FStar.Tc.Normalize.fst FStar.Tc.Errors.fst FStar.Tc.Rel.fst FStar.Tc.Util.fst FStar.Tc.Tc.fst \
	    	FStar.ToSMT.Term.fst FStar.ToSMT.Z3.fst FStar.ToSMT.SplitQueryCases.fst FStar.ToSMT.Encode.fst \
	    	FStar.TypeChecker.Common.fst FStar.TypeChecker.Env.fst FStar.TypeChecker.Normalize.fst FStar.TypeChecker.Errors.fst FStar.TypeChecker.Rel.fst FStar.TypeChecker.Util.fst FStar.TypeChecker.DMFF.fst FStar.TypeChecker.TcTerm.fst FStar.TypeChecker.Tc.fst \
		FStar.Parser.AST.fst FStar.Parser.DesugarEnv.fst FStar.Parser.Desugar.fst FStar.Parser.Env.fst FStar.Parser.Interleave.fst FStar.Parser.ToSyntax.fst FStar.Parser.Parse.fsti FStar.Parser.Lexhelp.fst FStar.Parser.ParseIt.fsti FStar.Parser.Driver.fst FStar.Parser.Dep.fst \
		FStar.Extraction.ML.Syntax.fst FStar.Extraction.ML.Env.fst FStar.Extraction.ML.UEnv.fst FStar.Extraction.ML.Util.fst FStar.Extraction.ML.Code.fst FStar.Extraction.ML.ExtractTyp.fst FStar.Extraction.ML.ExtractExp.fst FStar.Extraction.ML.ExtractMod.fst FStar.Extraction.ML.Term.fst FStar.Extraction.ML.Modul.fst FStar.Extraction.Kremlin.fst \
		FStar.Fsdoc.Generator.fst \
	    	FStar.SMTEncoding.Term.fst FStar.SMTEncoding.Util.fst FStar.SMTEncoding.Z3.fst FStar.SMTEncoding.SplitQueryCases.fst FStar.SMTEncoding.ErrorReporting.fst FStar.SMTEncoding.Encode.fst FStar.SMTEncoding.Solver.fst \
	    	FStar.Dependences.fst FStar.Interactive.fst FStar.Stratified.fst FStar.Universal.fst FStar.FStar.fst

ADMITTED_MODULES=System System.IO System.Text System.Diagnostics System.Collections.Generic Collections FStar.Heap FStar.ST FStar.All FStar.List FStar.Option FStar.Char FStar.String FStar.List FStar.Bytes FStar.Platform FStar.Util FStar.Version FStar.Getopt FStar.Range FStar.Unionfind FStar.Parser.ParseIt FStar.Parser.Parse FStar.Pprint
ADMITS=$(addprefix --admit_fsi , $(ADMITTED_MODULES))

FSTAROPTS=

all_boot_fsts:
	./tools/make_all_boot_fsts "$(BOOT_ALL)"

boot_fstis/prettyprint.fsti: prettyprint/prettyprint.fsti
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

$(LIB)/FStar.GetOpt.fsti: basic/getoptsimple.fsi
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
	+make -C ocaml-output clean
	+make -C ocaml-output all

# --------------------------------------------------------------------
# Bootstrapping in F#
# --------------------------------------------------------------------

BASELIBS    = $(addprefix -r , $(FSHARP_LIBS) $(OTHER_DLLS))
FS_SUPPORT_LIBS=native_int/prims.fs st.fs all.fs option.fs
FSTAR_SUPPORT_LIBS=char.fsi char.fs string.fsi string.fs list.fsi list.fs util.fsi util.fs platform.fsi platform.fs bytes.fsi bytes.fs range.fsi range.fs getoptsimple.fsi getoptsimple.fs version.fsi version.fs unionfind.fsi unionfind.fs
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

wc-boot:
	wc -l $(BOOT_ALL)

ctags:
	ctags --exclude=boot_fsts --exclude=boot_fstis --exclude=ocaml-output -R .
