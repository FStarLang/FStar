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
	$(FSTAR) --odir out --codegen FSharp hello.fst
	cp $(FS_LIBS) out
	$(FSC) --nowarn:0086 -o out/hello.exe $(LIB)/fs/prims.fs $(LIB)/fs/io.fs out/Hello.fs
	$(FSRUNTIME) ./out/hello.exe

ocaml: out hello.fst
	$(FSTAR) --odir out --codegen OCaml hello.fst
	cp $(LIB)/ml/prims.ml $(LIB)/ml/FStar_IO.ml out
	(cd out; ocamlc -o hello.exe nums.cma prims.ml FStar_IO.ml Hello.ml)
	./out/hello.exe

out:
	mkdir -p out

clean:
	rm -rf out
	rm -f *~
