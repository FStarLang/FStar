# -*- Makefile -*-

# --------------------------------------------------------------------
BASIC=prims-fake.fs profiling.fs util.fsi util.fs bytes.fsi bytes.fs range.fsi range.fs getoptsimple.fsi getoptsimple.fs platform.fsi platform.fs options.fs unionfind.fsi unionfind.fs lazyset.fsi lazyset.fs
BASIC_SRC=$(addprefix basic/, $(BASIC))

ABSYN=syntax.fs const.fs visit.fs util.fs print.fs 
ABSYN_SRC=$(addprefix absyn/, $(ABSYN))

FORMAT=format.fsi format.fs
FORMAT_SRC=$(addprefix format/, $(FORMAT))

BACKEND=nameenv.fsi nameenv.fs ocaml-syntax.fs ocaml-asttrans.fsi ocaml-asttrans.fs ocaml-codegen.fsi ocaml-codegen.fs
BACKEND_SRC=$(addprefix backend/, $(BACKEND))

JSBACKEND=ast.fs print.fs translate.fs
JSBACKEND_SRC=$(addprefix jsbackend/, $(JSBACKEND))

PARSER=ast.fs parse.fs lexhelp.fs lex.fs dsenv.fsi dsenv.fs desugar.fsi desugar.fs parseit.fsi parseit.fs driver.fs
PARSER_SRC=$(addprefix parser/, $(PARSER))
PARSER_NOGEN=ast.fs parse.fsy lexhelp.fs lex.fsl dsenv.fs desugar.fs parseit.fsi parseit.fs driver.fs
PARSER_NOGEN_SRC=$(addprefix parser/, $(PARSER_NOGEN))

TOSMT=term.fsi term.fs z3.fs encode.fs
TOSMT_SRC=$(addprefix tosmt/, $(TOSMT))

TC=errors.fs tcenv.fsi tcenv.fs normalize.fsi normalize.fs rel.fsi rel.fs tcutil.fsi tcutil.fs tc.fs
TC_SRC=$(addprefix tc/, $(TC))

# --------------------------------------------------------------------
PLATFORM=
BUILD_VERSION=
OTHERFLAGS=--optimize+ --debug:full --nologo -g -O --mlcompatibility $(addprefix --define:, $(BUILD_VERSION))

LIB=../lib
BIN=../bin
ALL_DLLS=basic.dll format.dll absyn.dll backend.dll parser.dll tc.dll tosmt.dll jsbackend.dll
FSHARP_LIBS=$(BIN)/FSharp.PowerPack.dll $(BIN)/FSharp.PowerPack.Compatibility.dll 
OTHER_DLLS=
BASELIBS=$(addprefix -r , $(FSHARP_LIBS) $(OTHER_DLLS))
RUNTIMEFLAGS=-g --nowarn:62

# --------------------------------------------------------------------
PLATFORM       =
RELEASE       ?= Debug
BUILD_VERSION  =
OTHERFLAGS    := --optimize+ --debug:full --nologo -g -O
OTHERFLAGS    += --mlcompatibility $(addprefix --define:, $(BUILD_VERSION))

ALL_DLLS    = basic.dll format.dll absyn.dll backend.dll parser.dll tc.dll tosmt.dll jsbackend.dll
FSHARP_LIBS = $(BIN)/FSharp.PowerPack.dll $(BIN)/FSharp.PowerPack.Compatibility.dll 
OTHER_DLLS  =
BASELIBS    = $(addprefix -r , $(FSHARP_LIBS) $(OTHER_DLLS))

# --------------------------------------------------------------------
ifeq ($(PLATFORM), X86)
override OTHERFLAGS += --platform:x86
endif

ifeq ($(OS),Windows_NT)
RUNTIME =
FSC     = fsc
MSBUILD = msbuild
else
RUNTIME = mono
FSC     = fsharpc
MSBUILD = xbuild
endif

MSBUILD := $(MSBUILD) /verbosity:normal

# --------------------------------------------------------------------
FSLYDIR := ../VS/packages/FsLexYacc.6.0.3
FSYACC  := $(RUNTIME) $(FSLYDIR)/bin/fsyacc.exe
FSLEX   := $(RUNTIME) $(FSLYDIR)/bin/fslex.exe

# --------------------------------------------------------------------
.PHONY: all z3_x86 z3_x64 wc clean tidy check
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

BACKEND_DEPS=$(addprefix $(BIN)/, basic.dll absyn.dll format.dll)
$(BIN)/backend.dll: $(BACKEND_DEPS) $(BACKEND_SRC)
	$(FSC) $(OTHERFLAGS) -a -o $@ $(BASELIBS) $(addprefix -r , $(BACKEND_DEPS)) $(BACKEND_SRC)

JSBACKEND_DEPS=$(addprefix $(BIN)/, basic.dll absyn.dll format.dll)
$(BIN)/jsbackend.dll: $(JSBACKEND_DEPS) $(JSBACKEND_SRC)
	$(FSC) $(OTHERFLAGS) -a -o $@ $(BASELIBS) $(addprefix -r , $(JSBACKEND_DEPS)) $(JSBACKEND_SRC)

PARSER_DEPS=$(addprefix $(BIN)/, basic.dll absyn.dll)
$(BIN)/parser.dll: $(PARSER_DEPS) $(PARSER_SRC)
	$(FSC)  $(OTHERFLAGS) -a -o $@ $(BASELIBS) $(addprefix -r , $(PARSER_DEPS)) $(PARSER_SRC)

TOSMT_DEPS=$(addprefix $(BIN)/, basic.dll absyn.dll tc.dll) 
$(BIN)/tosmt.dll: $(TOSMT_DEPS) $(TOSMT_SRC)
	$(FSC)  $(OTHERFLAGS) -a -o $@ $(BASELIBS) $(addprefix -r , $(TOSMT_DEPS)) $(TOSMT_SRC)

TC_DEPS=$(addprefix $(BIN)/, basic.dll absyn.dll)
$(BIN)/tc.dll: $(TC_DEPS) $(TC_SRC)
	$(FSC)  $(OTHERFLAGS) -a -o $@ $(BASELIBS) $(addprefix -r , $(TC_DEPS)) $(TC_SRC)

FSTAR_DEPS=$(addprefix $(BIN)/, $(ALL_DLLS))
$(BIN)/fstar.exe: $(FSTAR_DEPS) fstar.fs 
	$(FSC)  $(OTHERFLAGS) -o $@ $(BASELIBS) $(addprefix -r , $(FSTAR_DEPS)) fstar.fs 

fstar-nodeps: fstar.fs 
	$(FSC) $(OTHERFLAGS) -o $(BIN)/fstar.exe $(BASELIBS) $(addprefix -r , $(FSTAR_DEPS)) fstar.fs 


wc: $(BASIC_SRC) $(ABSYN_SRC) $(PARSER_NOGEN_SRC) $(TC_SRC) $(TOSMT_SRC) $(FORMAT_SRC) $(BACKEND_SRC) $(JSBACKEND_SRC) fstar.fs
	wc -l $^

clean:
	rm -rf *.exe $(addprefix $(BIN)/, $(ALL_DLLS) FStar.exe) *~ *res
	rm -rf $(BIN)/*.pdb  $(BIN)/*.mdb $(BIN)/queries

# --------------------------------------------------------------------
# Bootstrapping
# --------------------------------------------------------------------

STDFILES=system.fst st.fst list.fst option.fst string.fst
STDLIB=$(addprefix ../lib/, $(STDFILES))

BOOT_BASICFILES=bytes.fst platform.fsi util.fsi getoptsimple.fst options.fs range.fst unionfind.fst lazyset.fsi lazyset.fs
BOOT_BASIC=$(addprefix basic/, $(BOOT_BASICFILES))
BOOT_SYNTAXFILES=syntax.fsi syntax.fs const.fs visit.fs util.fs print.fs
BOOT_SYNTAX=$(addprefix absyn/, $(BOOT_SYNTAXFILES))
BOOT_PARSERFILES=ast.fs dsenv.fsi dsenv.fs desugar.fsi desugar.fs parse.fst lexhelp.fs parseit.fst driver.fs 
BOOT_PARSER=$(addprefix parser/, $(BOOT_PARSERFILES))
BOOT_TCFILES=errors.fs tcenv.fsi tcenv.fs normalize.fsi normalize.fs rel.fsi rel.fs tcutil.fsi tcutil.fs tc.fs
BOOT_TC=$(addprefix tc/, $(BOOT_TCFILES))
BOOT_FORMATFILES=format.fsi format.fs
BOOT_FORMAT=$(addprefix format/, $(BOOT_FORMATFILES))
BOOT_BACKENDFILES=nameenv.fsi nameenv.fs syntax.fs ocaml-asttrans.fsi ocaml-asttrans.fs ocaml-codegen.fsi ocaml-codegen.fs oaml.fsi ocaml.fs
BOOT_BACKEND=$(addprefix backend/, ocaml-backend-stub.fst)
BOOT_JSBACKENDFILES=ast.fs translate.fs
BOOT_JSBACKEND=$(addprefix jsbackend/, $(BOOT_JSBACKENDFILES))
BOOT_MAIN=fstar.fs
BOOT_ALL=$(STDLIB) $(BOOT_BASIC) $(BOOT_SYNTAX) $(BOOT_PARSER) $(BOOT_TC) $(TOSMT_SRC) $(BOOT_BACKEND) $(BOOT_JSBACKEND)

boot: $(BOOT_ALL)
	$(RUNTIME) ../bin/fstar.exe --fstar_home .. $(FSTAROPTS) --debug low --admit_fsi Microsoft.FStar.Util --admit_fsi Microsoft.FStar.Platform $^



test: boot
# CH: added minus in front of the commands that are expected to fail
#     now can we please make --verify actually fail when it couldn't discharge all obligations
	-make -C ../examples/unit-tests all-lax all-ver 
	@echo "--------Expect 16 failing assertions--------------"

wc-boot:
	wc -l $(BOOT_ALL)
