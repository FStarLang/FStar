# For simplified Makefiles, define FSTAR_HOME, then include the file below.
FSTAR_HOME=../..
include $(FSTAR_HOME)/ulib/ml/Makefile.include

# This target is very concise and re-uses the variables defined in
# Makefile.include. You shouldn't need to call `cp` ever.
ocaml: out hello.fst
	$(MAKE) -C $(ULIB_ML)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --universes hello.fst
	$(OCAMLOPT) out/Hello.ml -o hello.exe
	./hello.exe

# This target demonstrates how to compile with native_ints: the recursive
# invocation of $(MAKE) changes, and so do the include paths for `ocamlopt`.
# In this particular case, we need to compile against the extracted version of
# `FStar.Seq` (it is not realized in ML), so we pass it to `ocamlopt`.
testseq: out testseq.fst
	$(MAKE) -C $(ULIB_ML) PRIMS_DIR=native_int
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --use_native_int --odir out --codegen OCaml testseq.fst
	$(OCAMLOPT) -I $(ULIB_ML)/native_int -I out/ out/FStar_Seq.ml out/TestSeq.ml -o testseq.exe
	./testseq.exe

LIB=../../lib
BIN=../../bin
FSTAR=../../bin/fstar.exe

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

fs: out hello.fst
	$(FSTAR)   --odir out --codegen FSharp hello.fst
	cp $(FS_LIBS) out
	$(FSC) --nowarn:0086 -o out/hello.exe $(LIB)/fs/prims.fs $(LIB)/fs/io.fs out/Hello.fs
	$(FSRUNTIME) ./out/hello.exe

bat_testseq: out testseq.fst
	$(FSTAR) --use_native_int --odir out --codegen OCaml testseq.fst
	cp $(LIB)/ml/native_int/prims.ml $(LIB)/ml/FStar_IO.ml FStar_Seq.ml out
	(cd out; ocamlfind ocamlc -package batteries -linkpkg -g -o testseq.exe nums.cma prims.ml FStar_IO.ml FStar_Seq.ml TestSeq.ml)
	./out/TestSeq.exe

out:
	mkdir -p out

clean:
	make -C $(ULIB_ML) clean
	rm -rf out
	rm -f *~
