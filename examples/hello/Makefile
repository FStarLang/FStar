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

MLLIB=$(LIB)/ml

fs: out hello.fst
	$(FSTAR)   --odir out --codegen FSharp hello.fst
	cp $(FS_LIBS) out
	$(FSC) --nowarn:0086 -o out/hello.exe $(LIB)/fs/prims.fs $(LIB)/fs/io.fs out/Hello.fs
	$(FSRUNTIME) ./out/hello.exe

ocaml: out hello.fst
	$(MAKE) -C $(MLLIB)
	$(FSTAR)  --odir out --codegen OCaml hello.fst
	(cd out; ocamlfind ocamlopt -o hello.exe -package num -I ../$(MLLIB) ../$(MLLIB)/fstarlib.cmxa Hello.ml)
	./out/hello.exe

testseq: out testseq.fst
	$(MAKE) -C $(MLLIB) PRIMS_DIR=native_int
	$(FSTAR) --use_native_int --odir out --codegen OCaml testseq.fst
	(cd out; ocamlfind ocamlopt -o testseq.exe -I ../$(MLLIB) ../$(MLLIB)/fstarlib.cmxa FStar_All.ml FStar_Seq.ml TestSeq.ml)
	./out/TestSeq.exe

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
