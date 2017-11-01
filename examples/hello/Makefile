# For simplified Makefiles, define FSTAR_HOME, then include the file below.
FSTAR_HOME=../..
include ../Makefile.include

all: ocaml

include $(FSTAR_HOME)/ulib/ml/Makefile.include

ulib: ../../bin/fstarlib/fstarlib.cmxa

../../bin/fstarlib/fstarlib.cmxa:
	$(MAKE) -C $(ULIB_ML)



# This target is very concise and re-uses the variables defined in
# Makefile.include. You shouldn't need to call `cp` ever.
ocaml: out hello.fst ulib
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml hello.fst
	$(OCAMLOPT) out/Hello.ml -o hello.exe
	./hello.exe

# This target demonstrates how to compile with native_ints: the recursive
# invocation of $(MAKE) changes, and so do the include paths for `ocamlopt`.
# In this particular case, we need to compile against the extracted version of
# `FStar.Seq` (it is not realized in ML), so we pass it to `ocamlopt`.
testseq: out testseq.fst
	$(MAKE) -C $(ULIB_ML) PRIMS_DIR=native_int
        # CH: This target is broken: the --use_native_int flag no longer exists
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --use_native_int --odir out --codegen OCaml testseq.fst
        # CH: reference to $(ULIB_ML)/native_int is now bogus, there is no such thing
	$(OCAMLOPT) -I $(ULIB_ML)/native_int -I out/ out/FStar_Seq.ml out/TestSeq.ml -o testseq.exe
	./testseq.exe

LIB=$(FSTAR_HOME)/ulib
BIN=$(FSTAR_HOME)/bin

ifeq ($(OS),Windows_NT)
FSC     = fsc --mlcompatibility
else
FSC     = fsharpc --mlcompatibility
endif

ifeq ($(OS),Windows_NT)
FSRUNTIME =
else
FSRUNTIME = mono
endif

fs: out hello.fst
	$(FSTAR)   --odir out --codegen FSharp hello.fst
	$(FSRUNTIME) ./out/hello.exe

# CH: this target is dead, there is no ml/native_int anywhere
bat_testseq: out testseq.fst
	$(FSTAR) --use_native_int --odir out --codegen OCaml testseq.fst
	cp $(LIB)/ml/native_int/prims.ml $(LIB)/ml/FStar_IO.ml FStar_Seq.ml out
	(cd out; ocamlfind ocamlc -package batteries -linkpkg -g -o testseq.exe nums.cma prims.ml FStar_IO.ml FStar_Seq.ml TestSeq.ml)
	./out/TestSeq.exe

out:
	mkdir -p out

clean:
	rm -rf out
	rm -f *~
