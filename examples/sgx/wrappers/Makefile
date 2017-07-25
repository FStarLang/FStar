# For simplified Makefiles, define FSTAR_HOME, then include the file below.
FSTAR_HOME=/home/t-angoll/everest/FStar/
include ../../Makefile.include

all: GenWrapper.uver Gen_U_Wrapper.uver

include $(FSTAR_HOME)/ulib/ml/Makefile.include

OCAMLOPT_BARE=OCAMLPATH="../../../bin" ocamlfind opt
OCAMLOPT_=$(OCAMLOPT_BARE) -package fstarlib -linkpkg -g

# This target is very concise and re-uses the variables defined in
# Makefile.include. You shouldn't need to call `cp` ever.
vwrapper: out GenWrapper.fst
	$(MAKE) -C $(ULIB_ML)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml GenWrapper.fst
	$(OCAMLOPT) -I out out/Manifest.ml  out/WrapperUtil.ml out/GenWrapper.ml -o GenWrapper.exe
	./GenWrapper.exe

# This target is very concise and re-uses the variables defined in
# Makefile.include. You shouldn't need to call `cp` ever.
uwrapper: out Gen_U_Wrapper.fst
	$(MAKE) -C $(ULIB_ML)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml Gen_U_Wrapper.fst
	$(OCAMLOPT) -I out out/Manifest.ml out/WrapperUtil.ml out/Gen_U_Wrapper.ml -o GenUWrapper.exe
	./GenUWrapper.exe

LIB=$(FSTAR_HOME)/ulib
BIN=$(FSTAR_HOME)/bin

ifeq ($(OS),Windows_NT)
FSC     = fsc --mlcompatibility $(addprefix -r , $(FS_LIBS))
else
FSC     = fsharpc --mlcompatibility $(addprefix -r , $(FS_LIBS))
endif

ifeq ($(OS),Windows_NT)
FSRUNTIME =
else
FSRUNTIME = mono
endif

FS_LIBS=$(BIN)/FSharp.PowerPack.dll

out:
	mkdir -p out

clean:
	make -C $(ULIB_ML) clean
	rm -rf out
	rm -f *~
