# -*- Makefile -*-

# --------------------------------------------------------------------
BASIC=prims-fake.fs profiling.fs util.fsi util.fs bytes.fsi bytes.fs range.fsi range.fs getoptsimple.fsi getoptsimple.fs platform.fsi platform.fs options.fs unionfind.fsi unionfind.fs lazyset.fsi lazyset.fs
BASIC_SRC=$(addprefix basic/, $(BASIC))

ABSYN=syntax.fs const.fs visit.fs util.fs print.fs ssyntax.fs
ABSYN_SRC=$(addprefix absyn/, $(ABSYN))

FORMAT=format.fsi format.fs
FORMAT_SRC=$(addprefix format/, $(FORMAT))

BACKEND=nameenv.fsi nameenv.fs ocaml-syntax.fs ocaml-asttrans.fsi ocaml-asttrans.fs ocaml-codegen.fsi ocaml-codegen.fs
BACKEND_SRC=$(addprefix backend/, $(BACKEND))

JSBACKEND=ast.fs print.fs translate.fs
JSBACKEND_SRC=$(addprefix jsbackend/, $(JSBACKEND))

PARSER=ast.fs parseutil.fs parse.fs lexhelp.fs lex.fs dsenv.fsi dsenv.fs desugar.fsi desugar.fs parseit.fsi parseit.fs driver.fs
PARSER_SRC=$(addprefix parser/, $(PARSER))
PARSER_NOGEN=ast.fs parseutil.fs parse.fsy lexhelp.fs lex.fsl dsenv.fs desugar.fs parseit.fsi parseit.fs driver.fs
PARSER_NOGEN_SRC=$(addprefix parser/, $(PARSER_NOGEN))

TOSMT=term.fsi term.fs z3.fs encode.fs
TOSMT_SRC=$(addprefix tosmt/, $(TOSMT))

TC=tcenv.fsi tcenv.fs normalize.fsi normalize.fs errors.fs rel.fsi rel.fs tcutil.fsi tcutil.fs tc.fs
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
RUNTIMEFLAGS   = -g --nowarn:62

ALL_DLLS    = basic.dll format.dll absyn.dll backend.dll parser.dll tc.dll tosmt.dll jsbackend.dll
FSHARP_LIBS = System.Runtime.Serialization.dll System.Xml.dll $(BIN)/FSharp.PowerPack.dll $(BIN)/FSharp.PowerPack.Compatibility.dll $(BIN)/FSharp.PPrint.dll
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

STDFILES=system.fst stboot.fst list.fst option.fst string.fst char.fst
STDLIB=$(addprefix ../lib/, $(STDFILES))

BOOT_BASICFILES=bytes.fst platform.fsi util.fsi getoptsimple.fst options.fs range.fst unionfind.fst lazyset.fsi lazyset.fs
BOOT_BASIC=$(addprefix basic/, $(BOOT_BASICFILES))
BOOT_SYNTAXFILES=syntax.fsi syntax.fs const.fs visit.fs util.fs print.fs dssyntax.fs
BOOT_SYNTAX=$(addprefix absyn/, $(BOOT_SYNTAXFILES))
BOOT_PARSERFILES=ast.fs dsenv.fsi dsenv.fs desugar.fsi desugar.fs parse.fst lexhelp.fs parseit.fst driver.fs 
BOOT_PARSER=$(addprefix parser/, $(BOOT_PARSERFILES))
BOOT_TCFILES=tcenv.fsi tcenv.fs normalize.fsi normalize.fs errors.fs rel.fsi rel.fs tcutil.fsi tcutil.fs tc.fs
BOOT_TC=$(addprefix tc/, $(BOOT_TCFILES))
BOOT_FORMATFILES=format.fsi formatml.fs
BOOT_FORMAT=$(addprefix format/, $(BOOT_FORMATFILES))
BOOT_BACKENDFILES=nameenv.fsi nameenv.fs ocaml-syntax.fs ocaml-asttrans.fsi ocaml-asttrans.fs ocaml-codegen.fsi ocaml-codegen.fs
BOOT_BACKEND=$(addprefix backend/, $(BOOT_BACKENDFILES))
BOOT_JSBACKENDFILES=ast.fs translate.fs
BOOT_JSBACKEND=$(addprefix jsbackend/, $(BOOT_JSBACKENDFILES))
BOOT_MAIN=fstar.fs
BOOT_ALL=$(STDLIB) $(BOOT_BASIC) $(BOOT_SYNTAX) $(BOOT_PARSER) $(BOOT_TC) $(TOSMT_SRC) $(BOOT_FORMAT) $(BOOT_BACKEND) 

boot: $(BOOT_ALL)
	$(RUNTIME) ../bin/fstar.exe --lax --fstar_home .. $(FSTAROPTS) --debug_level Low --admit_fsi Microsoft.FStar.Util --admit_fsi Microsoft.FStar.Platform $^

ocaml: $(BOOT_ALL)
	$(RUNTIME) ../bin/fstar.exe --lax --odir ocaml-output --fstar_home .. $(FSTAROPTS) --codegen OCaml --debug_level Low --trace_error --admit_fsi Microsoft.FStar.Util --admit_fsi Microsoft.FStar.Platform $^

fstarml:
	@echo "Building parser and lexer filex..."
	make -C ocaml-output parser
	make -s -C ocaml-output

OCAML_FILES= Microsoft_FStar_Options.ml Microsoft_FStar_LazySet.ml Microsoft_FStar_Absyn_Syntax.ml Microsoft_FStar_Absyn_Const.ml Microsoft_FStar_Absyn_Visit.ml Microsoft_FStar_Absyn_Util.ml Microsoft_FStar_Absyn_Print.ml Microsoft_FStar_Absyn_SSyntax.ml Microsoft_FStar_Parser_AST.ml Microsoft_FStar_Parser_DesugarEnv.ml Microsoft_FStar_Parser_Desugar.ml Microsoft_FStar_Parser_Parse.ml Microsoft_FStar_Parser_Lexhelp.ml Microsoft_FStar_Parser_Driver.ml Microsoft_FStar_Tc_Env.ml Microsoft_FStar_Tc_Normalize.ml Microsoft_FStar_Tc_Errors.ml Microsoft_FStar_Tc_Rel.ml Microsoft_FStar_Tc_Util.ml Microsoft_FStar_Tc_Tc.ml Microsoft_FStar_ToSMT_Term.ml Microsoft_FStar_ToSMT_Z3.ml Microsoft_FStar_ToSMT_Encode.ml 
OCAML_ALL=$(addprefix ocaml-output/, $(OCAML_FILES))

test:   boot
	make -s -C ../examples/unit-tests all-lax 
	make -s -C ../examples/unit-tests vector
	make -s -C ../examples/unit-tests mergesort.vv
	make -s -C ../examples/unit-tests rpc
	make -s -C ../examples/unit-tests acls2
	make -s -C ../examples/unit-tests counters
	-make -s -C ../examples/unit-tests all-ver 
	@echo "--------Expect 20 errors--------------"


test.diff:
	@make -s test | grep -v "^make\[" > .test.out
	@diff .test.out expected-test-output
	@echo "F* ok"

wc-boot:
	wc -l $(BOOT_ALL)
