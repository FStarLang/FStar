# -*- Makefile -*-

# --------------------------------------------------------------------
BASIC=prims-fake.fs profiling.fs char.fsi char.fs string.fsi string.fs list.fsi list.fs util.fsi util.fs bytes.fsi bytes.fs range.fsi range.fs getoptsimple.fsi getoptsimple.fs platform.fsi platform.fs version.fsi version.fs options.fs unionfind.fsi unionfind.fs
BASIC_SRC=$(addprefix basic/, $(BASIC))

ABSYN=syntax.fs const.fs visit.fs util.fs print.fs ssyntax.fs
ABSYN_SRC=$(addprefix absyn/, $(ABSYN))

FORMAT=format.fsi format.fs
FORMAT_SRC=$(addprefix format/, $(FORMAT))

EXTRACTION=ml-syntax.fs env.fs util.fs codegen.fsi codegen.fs extracttyp.fs extractexp.fs extractmod.fs
EXTRACTION_SRC=$(addprefix extraction/, $(EXTRACTION))

PARSER=ast.fs parseutil.fs parse.fs lexhelp.fs lex.fs dsenv.fsi dsenv.fs desugar.fsi desugar.fs parseit.fsi parseit.fs driver.fs
PARSER_SRC=$(addprefix parser/, $(PARSER))
PARSER_NOGEN=ast.fs parseutil.fs parse.fsy lexhelp.fs lex.fsl dsenv.fs desugar.fs parseit.fsi parseit.fs driver.fs
PARSER_NOGEN_SRC=$(addprefix parser/, $(PARSER_NOGEN))

TOSMT=term.fsi term.fs z3.fs splitcases.fs encode.fs
TOSMT_SRC=$(addprefix tosmt/, $(TOSMT))

TC=tcenv.fsi tcenv.fs recheck.fs normalize.fsi normalize.fs errors.fs rel.fsi rel.fs tcutil.fsi tcutil.fs tc.fs
TC_SRC=$(addprefix tc/, $(TC))

# --------------------------------------------------------------------
LIB=../lib
BIN=../bin

# --------------------------------------------------------------------
PLATFORM       =
RELEASE       ?= Debug
BUILD_VERSION  =
OTHERFLAGS    := --optimize+ --debug:full --nologo -g -O
OTHERFLAGS    += --mlcompatibility $(addprefix --define:, $(BUILD_VERSION))

ALL_DLLS    = basic.dll format.dll absyn.dll extraction.dll parser.dll tc.dll tosmt.dll
FSHARP_LIBS = System.Runtime.Serialization.dll System.Xml.dll $(BIN)/FSharp.PowerPack.dll $(BIN)/FSharp.PowerPack.Compatibility.dll $(BIN)/FSharp.PPrint.dll
OTHER_DLLS  =
BASELIBS    = $(addprefix -r , $(FSHARP_LIBS) $(OTHER_DLLS))

# --------------------------------------------------------------------
ifeq ($(PLATFORM), X86)
override OTHERFLAGS += --platform:x86
endif

ifeq ($(OS),Windows_NT)
FSC     = fsc
MSBUILD = msbuild
else
FSC     = fsharpc
MSBUILD = xbuild
endif

MSBUILD := $(MSBUILD) /verbosity:normal

# --------------------------------------------------------------------
ifeq ($(OS),Windows_NT)
RUNTIME =
else
RUNTIME = mono
endif

FSLYDIR := VS/packages/FsLexYacc.6.1.0
FSYACC  := $(RUNTIME) $(FSLYDIR)/build/fsyacc.exe
FSLEX   := $(RUNTIME) $(FSLYDIR)/build/fslex.exe

# --------------------------------------------------------------------
.PHONY: all z3_x86 z3_x64 wc clean tidy boot ocaml
.PHONY: msbuild msbuild-clean

# --------------------------------------------------------------------
all: $(BIN)/fstar.exe

# --------------------------------------------------------------------
z3-x86:
	cp $(BIN)/Microsoft.Z3.x86.dll $(BIN)/Microsoft.Z3.dll
	cp $(BIN)/z3.x86.dll $(BIN)/z3.dll

z3-x64:
	cp $(BIN)/Microsoft.Z3.x64.dll $(BIN)/Microsoft.Z3.dll
	cp $(BIN)/z3.x64.dll $(BIN)/z3.dll

# --------------------------------------------------------------------
msbuild:
	$(MAKE) -C VS install-packages
	$(MSBUILD) VS/FStar.sln

msbuild-clean:
	$(MSBUILD) /t:clean VS/FStar.sln

# --------------------------------------------------------------------
parser/parse.fs: parser/parse.fsy
	$(MAKE) -C VS install-packages
	$(FSYACC) --module FStar.Parser.Parse $<

parser/lex.fs: parser/lex.fsl
	$(MAKE) -C VS install-packages
	$(FSLEX) --unicode $<

BASIC_DEPS=
$(BIN)/basic.dll: $(BASIC_DEPS) $(BASIC_SRC)
	$(FSC)  $(OTHERFLAGS) -a -o $@ $(BASELIBS) $(addprefix -r , $(BASIC_DEPS)) $(BASIC_SRC)

ABSYN_DEPS=$(addprefix $(BIN)/, basic.dll)
$(BIN)/absyn.dll: $(ABSYN_DEPS) $(ABSYN_SRC)
	$(FSC)  $(OTHERFLAGS) -a -o $@ $(BASELIBS) $(addprefix -r , $(ABSYN_DEPS)) $(ABSYN_SRC)

ABSYN_DEPS=$(addprefix $(BIN)/, basic.dll)
$(BIN)/testAbsyn.exe: $(ABSYN_DEPS) $(ABSYN_SRC) absyn/test.fs
	$(FSC)  $(OTHERFLAGS) --define:TEST --define:DEBUG -o $@ $(BASELIBS) $(addprefix -r , $(ABSYN_DEPS)) $(ABSYN_SRC) absyn/test.fs

FORMAT_DEPS=
$(BIN)/format.dll: $(FORMAT_DEPS) $(FORMAT_SRC)
	$(FSC) $(OTHERFLAGS) -a -o $@ $(BASELIBS) $(addprefix -r , $(FORMAT_DEPS)) $(FORMAT_SRC)

EXTRACTION_DEPS=$(addprefix $(BIN)/, basic.dll absyn.dll format.dll tc.dll)
$(BIN)/extraction.dll: $(EXTRACTION_DEPS) $(EXTRACTION_SRC)
	$(FSC) $(OTHERFLAGS) -a -o $@ $(BASELIBS) $(addprefix -r , $(EXTRACTION_DEPS)) $(EXTRACTION_SRC)

PARSER_DEPS=$(addprefix $(BIN)/, basic.dll absyn.dll tc.dll)
$(BIN)/parser.dll: $(PARSER_DEPS) $(PARSER_SRC)
	$(FSC)  $(OTHERFLAGS) -a -o $@ $(BASELIBS) $(addprefix -r , $(PARSER_DEPS)) $(PARSER_SRC)

TOSMT_DEPS=$(addprefix $(BIN)/, basic.dll absyn.dll tc.dll)
$(BIN)/tosmt.dll: $(TOSMT_DEPS) $(TOSMT_SRC)
	$(FSC)  $(OTHERFLAGS) -a -o $@ $(BASELIBS) $(addprefix -r , $(TOSMT_DEPS)) $(TOSMT_SRC)

TC_DEPS=$(addprefix $(BIN)/, basic.dll absyn.dll)
$(BIN)/tc.dll: $(TC_DEPS) $(TC_SRC)
	$(FSC)  $(OTHERFLAGS) -a -o $@ $(BASELIBS) $(addprefix -r , $(TC_DEPS)) $(TC_SRC)

FSTAR_DEPS=$(addprefix $(BIN)/, $(ALL_DLLS))
$(BIN)/fstar.exe: $(FSTAR_DEPS) fstar/fstar.fs fstar/main.fs $(BIN)/fstar-mono.sh
ifeq ($(OS),Windows_NT)
	$(FSC)  $(OTHERFLAGS) -o $@ $(BASELIBS) $(addprefix -r , $(FSTAR_DEPS)) fstar/fstar.fs fstar/main.fs
else
	$(FSC)  $(OTHERFLAGS) -o $(BIN)/fstar-mono.exe $(BASELIBS) $(addprefix -r , $(FSTAR_DEPS)) fstar/fstar.fs fstar/main.fs
	cp $(BIN)/fstar-mono.sh $(BIN)/fstar.exe
endif


wc: $(BASIC_SRC) $(ABSYN_SRC) $(PARSER_NOGEN_SRC) $(TC_SRC) $(TOSMT_SRC) $(FORMAT_SRC) $(EXTRACTION_SRC) fstar/fstar.fs
	sloccount $^

clean:
	rm -rf *.exe $(addprefix $(BIN)/, $(ALL_DLLS) fstar.exe) *~ *res
	rm -rf $(BIN)/*.pdb  $(BIN)/*.mdb $(BIN)/queries
	make -s -C ocaml-output clean

# --------------------------------------------------------------------
# Bootstrapping in OCaml
# --------------------------------------------------------------------

STDFILESEXP=system.fst
STDFILES=system.fsi system.io.fsi system.text.fsi system.diagnostics.fsi system.collections.generic.fsi collections.fsi set.fsi allboot.fsti stboot.fsi list.fsi option.fsi
STDLIB=$(addprefix ../lib/, $(STDFILES))
STDLIBEXP=$(addprefix ../lib/, $(STDFILES))

BOOT_BASICFILES=char.fsi string.fsi bytes.fsti platform.fsi util.fsi getoptsimple.fsti range.fsti unionfind.fsti version.fsi options.fs
BOOT_BASIC=$(addprefix basic/, $(BOOT_BASICFILES))
BOOT_SYNTAXFILES=syntax.fsi syntax.fs const.fs visit.fs util.fs print.fs ssyntax.fs
BOOT_SYNTAX=$(addprefix absyn/, $(BOOT_SYNTAXFILES))
BOOT_PARSERFILES=ast.fs dsenv.fsi dsenv.fs desugar.fsi desugar.fs parse.fsti lexhelp.fs parseit.fsi driver.fs
BOOT_PARSER=$(addprefix parser/, $(BOOT_PARSERFILES))
BOOT_TCFILES=tcenv.fsi tcenv.fs recheck.fs normalize.fsi normalize.fs errors.fs rel.fsi rel.fs tcutil.fsi tcutil.fs tc.fs
BOOT_TC=$(addprefix tc/, $(BOOT_TCFILES))
BOOT_FORMATFILES=format.fsi formatml.fs
BOOT_FORMAT=$(addprefix format/, $(BOOT_FORMATFILES))
BOOT_EXTRACTIONFILES=ml-syntax.fs env.fs util.fs codegen.fsi codegen.fs extracttyp.fs extractexp.fs extractmod.fs
BOOT_EXTRACTION=$(addprefix extraction/, $(BOOT_EXTRACTIONFILES))

BOOT_MAIN=fstar/fstar.fs
BOOT_ALL=$(STDLIB) $(BOOT_BASIC) $(BOOT_SYNTAX) $(BOOT_TC) $(BOOT_PARSER) $(TOSMT_SRC) $(BOOT_FORMAT) $(BOOT_EXTRACTION) $(BOOT_MAIN)

ADMITTED_MODULES=System System.IO System.Text System.Diagnostics System.Collections.Generic Collections FStar.Set FStar.Heap FStar.ST FStar.All FStar.List FStar.Option FStar.Char FStar.String FStar.List FStar.Bytes FStar.Platform FStar.Util FStar.Version FStar.Getopt FStar.Range FStar.Unionfind FStar.Parser.ParseIt FStar.Parser.Parse 
ADMITS=$(addprefix --admit_fsi , $(ADMITTED_MODULES))

ocaml: $(BOOT_ALL)
	../bin/fstar.exe --use_native_int --eager_inference --MLish --lax --fs_typ_app --odir ocaml-output $(FSTAROPTS) --codegen OCaml $(ADMITS) $^

ocaml-test: ocaml boot-ocaml

boot-ocaml:
	make -C ocaml-output

# --------------------------------------------------------------------
# Bootstrapping in F#
# --------------------------------------------------------------------

FS_SUPPORT_LIBS=native_int/prims.fs st.fs all.fs option.fs
FSTAR_SUPPORT_LIBS=char.fsi char.fs string.fsi string.fs list.fsi list.fs util.fsi util.fs platform.fsi platform.fs bytes.fsi bytes.fs range.fsi range.fs getoptsimple.fsi getoptsimple.fs version.fsi version.fs unionfind.fsi unionfind.fs
BOOT_FS_BASE=FStar.Options.fs
BOOT_FS_SYNTAX=FStar.Absyn.Syntax.fs FStar.Absyn.Const.fs FStar.Absyn.Visit.fs FStar.Absyn.Util.fs FStar.Absyn.Print.fs FStar.Absyn.SSyntax.fs
BOOT_FS_TC=FStar.Tc.Env.fs FStar.Tc.Recheck.fs FStar.Tc.Normalize.fs FStar.Tc.Errors.fs FStar.Tc.Rel.fs FStar.Tc.Util.fs FStar.Tc.Tc.fs 
BOOT_FS_PARSER=FStar.Parser.AST.fs parseutil.fs parse.fs FStar.Parser.Lexhelp.fs lex.fs FStar.Parser.DesugarEnv.fs FStar.Parser.Desugar.fs parseit.fs FStar.Parser.Driver.fs
BOOT_FS_TOSMT=FStar.ToSMT.Term.fs FStar.ToSMT.Z3.fs FStar.ToSMT.SplitQueryCases.fs FStar.ToSMT.Encode.fs
BOOT_FS_EXTRACTION=FStar.Extraction.ML.Syntax.fs FStar.Extraction.ML.Env.fs FStar.Extraction.ML.Util.fs FStar.Extraction.ML.Code.fs FStar.Extraction.ML.ExtractTyp.fs FStar.Extraction.ML.ExtractExp.fs FStar.Extraction.ML.ExtractMod.fs
BOOT_FS_FILES=FSharp.Format.fs $(BOOT_FS_BASE) $(BOOT_FS_SYNTAX) $(BOOT_FS_TC) $(BOOT_FS_PARSER) $(BOOT_FS_TOSMT) $(BOOT_FS_EXTRACTION) FStar.FStar.fs

boot-fsharp: fsharp-output fs plain-fs-files fsharp-output/fstar.exe 

fsharp-output/fstar.exe: $(addprefix ../lib/fs/, $(FS_SUPPORT_LIBS)) $(addprefix basic/, $(FSTAR_SUPPORT_LIBS)) $(addprefix fsharp-output/, $(BOOT_FS_FILES) main.fs)
	$(FSC) --nowarn:0025 -o $@ $(BASELIBS) $(OTHERFLAGS) $^

fs: $(BOOT_ALL) 
	../bin/fstar.exe --use_native_int --eager_inference --MLish --lax --fs_typ_app --odir fsharp-output $(FSTAROPTS) --codegen FSharp $(ADMITS) $^

fsharp-output: 
	mkdir -p fsharp-output
	make -C VS install-packages
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

test:   clean $(BIN)/fstar.exe ocaml-test
	make -C ../lib
	make -C ../examples
	make -C ../examples/hello ocaml
	make -C ../contrib/Platform/ml/
	make -C ../contrib/CoreCrypto/ml/ all test
	make -C ../examples/crypto clean rpc-test cnt-test
	make -C ../examples/wysteria a.out distclean

test.net: clean $(BIN)/fstar.exe boot
	make -C ../examples

test.diff:
	@make -s test | grep -v "^make\[" > .test.out
	@diff .test.out expected-test-output
	@echo "F* ok"

wc-boot:
	wc -l $(BOOT_ALL)
