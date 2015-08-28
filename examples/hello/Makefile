LIB=../../lib
BIN=../../bin
FSC=fsc --mlcompatibility $(addprefix -r , $(FS_LIBS))
FS_LIBS=$(BIN)/FSharp.PowerPack.dll

fs: out hello.fst
	fstar --odir out --codegen FSharp hello.fst
	cp $(FS_LIBS) out
	$(FSC) -o out/hello.exe $(LIB)/fs/prims.fs $(LIB)/fs/io.fs out/hello.fs
	./out/hello.exe

ocaml: out hello.fst
	fstar --odir out --codegen OCaml hello.fst
	cp $(LIB)/ml/prims.ml $(LIB)/ml/FStar_IO.ml out
	(cd out; ocamlc -o hello.exe prims.ml FStar_IO.ml Hello.ml)
	./out/hello.exe

out:
	mkdir -p out


clean:
	rm -rf out
	rm -f *~
