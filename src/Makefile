# -*- Makefile -*-

# --------------------------------------------------------------------
BASIC=prims-fake.fs profiling.fs util.fsi util.fs bytes.fsi bytes.fs range.fsi range.fs getoptsimple.fsi getoptsimple.fs platform.fsi platform.fs options.fs unionfind.fsi unionfind.fs
BASIC_SRC=$(addprefix basic/, $(BASIC))

ABSYN=syntax.fs const.fs visit.fs util.fs print.fs ssyntax.fs
ABSYN_SRC=$(addprefix absyn/, $(ABSYN))

FORMAT=format.fsi format.fs
FORMAT_SRC=$(addprefix format/, $(FORMAT))

BACKEND=nameenv.fsi nameenv.fs ml-syntax.fs ocaml-codegen.fsi ocaml-codegen.fs ocaml-asttrans.fsi ocaml-asttrans.fs
BACKEND_SRC=$(addprefix backend/, $(BACKEND))

EXTRACTION=ml-syntax.fs env.fs util.fs ocaml-codegen.fsi ocaml-codegen.fs extracttyp.fs extractexp.fs extractmod.fs wextract.fs
EXTRACTION_SRC=$(addprefix extraction/, $(EXTRACTION))

JSBACKEND=ast.fs print.fs translate.fs
JSBACKEND_SRC=$(addprefix jsbackend/, $(JSBACKEND))

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

ALL_DLLS    = basic.dll format.dll absyn.dll backend.dll extraction.dll parser.dll tc.dll tosmt.dll #jsbackend.dll
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

FSLYDIR := ../VS/packages/FsLexYacc.6.0.3
FSYACC  := $(RUNTIME) $(FSLYDIR)/bin/fsyacc.exe
FSLEX   := $(RUNTIME) $(FSLYDIR)/bin/fslex.exe

# --------------------------------------------------------------------
.PHONY: all z3_x86 z3_x64 wc clean tidy boot ocaml
.PHONY: msbuild msbuild-clean

# --------------------------------------------------------------------
all: $(BIN)/fstar.exe

# --------------------------------------------------------------------
z3_x86:
	cp $(BIN)/Microsoft.Z3.x86.dll $(BIN)/Microsoft.Z3.dll
	cp $(BIN)/z3.x86.dll $(BIN)/z3.dll

z3_x64:
	cp $(BIN)/Microsoft.Z3.x64.dll $(BIN)/Microsoft.Z3.dll
	cp $(BIN)/z3.x64.dll $(BIN)/z3.dll

# --------------------------------------------------------------------
msbuild:
	$(MAKE) -C ../VS install-packages
	$(MSBUILD) ../VS/FStar.sln

msbuild-clean:
	$(MSBUILD) /t:clean ../VS/FStar.sln

# --------------------------------------------------------------------
parser/parse.fs: parser/parse.fsy
	$(MAKE) -C ../VS install-packages
	$(FSYACC) --module Microsoft.FStar.Parser.Parse $<

parser/lex.fs: parser/lex.fsl
	$(MAKE) -C ../VS install-packages
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

BACKEND_DEPS=$(addprefix $(BIN)/, basic.dll absyn.dll format.dll tc.dll)
$(BIN)/backend.dll: $(BACKEND_DEPS) $(BACKEND_SRC)
	$(FSC) $(OTHERFLAGS) -a -o $@ $(BASELIBS) $(addprefix -r , $(BACKEND_DEPS)) $(BACKEND_SRC)

EXTRACTION_DEPS=$(addprefix $(BIN)/, basic.dll absyn.dll format.dll tc.dll)
$(BIN)/extraction.dll: $(EXTRACTION_DEPS) $(EXTRACTION_SRC)
	$(FSC) $(OTHERFLAGS) -a -o $@ $(BASELIBS) $(addprefix -r , $(EXTRACTION_DEPS)) $(EXTRACTION_SRC)

JSBACKEND_DEPS=$(addprefix $(BIN)/, basic.dll absyn.dll format.dll)
$(BIN)/jsbackend.dll: $(JSBACKEND_DEPS) $(JSBACKEND_SRC)
	$(FSC) $(OTHERFLAGS) -a -o $@ $(BASELIBS) $(addprefix -r , $(JSBACKEND_DEPS)) $(JSBACKEND_SRC)

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
$(BIN)/fstar.exe: $(FSTAR_DEPS) fstar.fs main.fs $(BIN)/fstar-mono.sh
ifeq ($(OS),Windows_NT)
	$(FSC)  $(OTHERFLAGS) -o $@ $(BASELIBS) $(addprefix -r , $(FSTAR_DEPS)) fstar.fs main.fs
else
	$(FSC)  $(OTHERFLAGS) -o $(BIN)/fstar-mono.exe $(BASELIBS) $(addprefix -r , $(FSTAR_DEPS)) fstar.fs main.fs
	cp $(BIN)/fstar-mono.sh $(BIN)/fstar.exe
endif

fstar-nodeps: fstar.fs main.fs
	$(FSC) $(OTHERFLAGS) -o $(BIN)/fstar.exe $(BASELIBS) $(addprefix -r , $(FSTAR_DEPS)) fstar.fs


wc: $(BASIC_SRC) $(ABSYN_SRC) $(PARSER_NOGEN_SRC) $(TC_SRC) $(TOSMT_SRC) $(FORMAT_SRC) $(BACKEND_SRC) $(EXTRACTION_SRC) $(JSBACKEND_SRC) fstar.fs
#	wc -l $^
	sloccount $^

clean:
	rm -rf *.exe $(addprefix $(BIN)/, $(ALL_DLLS) fstar.exe) *~ *res
	rm -rf $(BIN)/*.pdb  $(BIN)/*.mdb $(BIN)/queries
	make -s -C ocaml-output clean

# --------------------------------------------------------------------
# Bootstrapping
# --------------------------------------------------------------------

STDFILESEXP=system.fst
STDFILES=system.fsi system.io.fsi system.text.fsi system.diagnostics.fsi system.collections.generic.fsi collections.fsi set.fsi allboot.fsti stboot.fsi list.fsi option.fsi string.fsi char.fsi
STDLIB=$(addprefix ../lib/, $(STDFILES))
STDLIBEXP=$(addprefix ../lib/, $(STDFILES))

BOOT_BASICFILES=bytes.fsti platform.fsi util.fsi getoptsimple.fsti range.fsti unionfind.fsti options.fs
BOOT_BASIC=$(addprefix basic/, $(BOOT_BASICFILES))
BOOT_SYNTAXFILES=syntax.fsi syntax.fs const.fs visit.fs util.fs print.fs ssyntax.fs
BOOT_SYNTAX=$(addprefix absyn/, $(BOOT_SYNTAXFILES))
BOOT_PARSERFILES=ast.fs dsenv.fsi dsenv.fs desugar.fsi desugar.fs parse.fsti lexhelp.fs parseit.fsi driver.fs
BOOT_PARSER=$(addprefix parser/, $(BOOT_PARSERFILES))
BOOT_TCFILES=tcenv.fsi tcenv.fs recheck.fs normalize.fsi normalize.fs errors.fs rel.fsi rel.fs tcutil.fsi tcutil.fs tc.fs
BOOT_TC=$(addprefix tc/, $(BOOT_TCFILES))
BOOT_FORMATFILES=format.fsi formatml.fs
BOOT_FORMAT=$(addprefix format/, $(BOOT_FORMATFILES))
BOOT_BACKENDFILES=nameenv.fsi nameenv.fs ml-syntax.fs ocaml-codegen.fsi ocaml-codegen.fs ocaml-asttrans.fsi ocaml-asttrans.fs
BOOT_BACKEND=$(addprefix backend/, $(BOOT_BACKENDFILES))
BOOT_EXTRACTIONFILES=ml-syntax.fs env.fs util.fs ocaml-codegen.fsi ocaml-codegen.fs extracttyp.fs extractexp.fs extractmod.fs wextract.fs
BOOT_EXTRACTION=$(addprefix extraction/, $(BOOT_EXTRACTIONFILES))

BOOT_JSBACKENDFILES=ast.fs translate.fs
BOOT_JSBACKEND=$(addprefix jsbackend/, $(BOOT_JSBACKENDFILES))
BOOT_MAIN=fstar.fs
BOOT_ALL=$(STDLIB) $(BOOT_BASIC) $(BOOT_SYNTAX) $(BOOT_TC) $(BOOT_PARSER) $(TOSMT_SRC) $(BOOT_FORMAT) $(BOOT_EXTRACTION) $(BOOT_BACKEND) fstar.fs

ADMITTED_MODULES=System System.IO System.Text System.Diagnostics System.Collections.Generic Collections Set Heap ST All List Option String Char Microsoft.FStar.Bytes Microsoft.FStar.Platform Microsoft.FStar.Util Microsoft.FStar.Getopt Microsoft.FStar.Range Microsoft.FStar.Unionfind Microsoft.FStar.Parser.ParseIt Microsoft.FStar.Parser.Parse
ADMITS=$(addprefix --admit_fsi , $(ADMITTED_MODULES))
boot: $(BOOT_ALL)
	../bin/fstar.exe --debug yes --fs_typ_app --lax $(FSTAROPTS) $(ADMITS) $^

ocaml: $(BOOT_ALL)
	../bin/fstar.exe --eager_inference --MLish --lax --fs_typ_app --odir ocaml-output $(FSTAROPTS) --codegen OCaml-experimental $(ADMITS) $^

ocaml-experimental: $(BOOT_ALL)
	../bin/fstar.exe --eager_inference --MLish --lax --fs_typ_app --odir ocaml-output $(FSTAROPTS) --codegen OCaml-experimental $(ADMITS) $^

fstarml:
	@echo "Building parser and lexer filex..."
	make -C ocaml-output parser
	make -s -C ocaml-output

ocaml-test: ocaml boot-ocaml

boot-ocaml:
	make -C ocaml-output parser
	make -C ocaml-output

test:   clean $(BIN)/fstar.exe ocaml-test
	make -C ../lib
	make -C ../examples

test.net: clean $(BIN)/fstar.exe boot
	make -C ../examples

test.diff:
	@make -s test | grep -v "^make\[" > .test.out
	@diff .test.out expected-test-output
	@echo "F* ok"

wc-boot:
	wc -l $(BOOT_ALL)
