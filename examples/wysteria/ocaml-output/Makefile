FSTAR_HOME=../../..

ifeq ($(OS),Windows_NT)
    # internally flexlink uses i686-w64-mingw32-gcc.exe
    CC = flexlink -chain mingw -v -v -exe -lgdi32
    # flexlink is needed to link in	/cygdrive/c/OCaml/bin/flexdll_initer_mingw.o /cygdrive/c/OCaml/bin/flexdll_mingw.o
    LIB = $(FSTAR_HOME)/3rdparty/win32 #place to look for libcrypto.a
else
    UNAME_S := $(shell uname -s)
    ifeq ($(UNAME_S),Darwin)
        CC = gcc
        LIB = $(FSTAR_HOME)/3rdparty/osx #place to look for libcrypto.a
    else
        CC = gcc
        LIB = $(FSTAR_HOME)/3rdparty/x86_64 #place to look for libcrypto.a
    endif
endif

OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/contrib/Platform/ml $(FSTAR_HOME)/contrib/CoreCrypto/ml $(FSTAR_HOME)/lib/ml/native_int $(FSTAR_HOME)/lib/ml)

OCAMLC=ocamlfind ocamlopt -cc "$(CC)" -cclib -L$(LIB) -cclib -lcrypto -package batteries -linkpkg -g -thread


a.out:
	make -C $(FSTAR_HOME)/contrib/
	cp $(FSTAR_HOME)/lib/ml/native_int/prims.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_ST.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_All.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_IO.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_List.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_String.ml .
	cp ../ml/ffibridge.ml .
	cp ../ml/runtime.ml .
	cp ../ml/interpreteriface.ml .
	cp ../ml/hashtable.ml .
	$(OCAMLC) $(OCAML_INCLUDE_PATHS) $(FSTAR_HOME)/contrib/Platform/ml/platform.cmx $(FSTAR_HOME)/contrib/CoreCrypto/ml/CoreCrypto.cmxa prims.ml FStar_Ghost.ml FStar_List_Tot.ml FStar_ST.ml FStar_All.ml FStar_List.ml FStar_OrdSet.ml FStar_OrdMap.ml FStar_IO.ml FStar_String.ml  \
	            Prins.ml AST.ml ffibridge.ml Semantics.ml PSemantics.ml RuntimeTheory.ml runtime.ml Print.ml hashtable.ml Circuit.ml SHA1.ml Crypto.ml Interpreter.ml SecServer.ml FFI.ml prog.ml interpreteriface.ml smciface.ml SMCMain.ml -o a.out

clean:
	rm -f *.cmi *.cmx *.o a.out circuit_* input_* output_* config* bar.txt

distclean: clean
	rm -f prims.ml FStar_Ghost.ml FStar_FunctionalExtensionality.ml FStar_List_Tot.ml FStar_Heap.ml FStar_ST.ml FStar_All.ml FStar_SeqProperties.ml FStar_List.ml FStar_ListProperties.ml FStar_OrdSet.ml FStar_OrdMap.ml FStar_Classical.ml FStar_IO.ml FStar_String.ml Prins.ml AST.ml Semantics.ml PSemantics.ml RuntimeTheory.ml Platform_Bytes.ml CoreCrypto.ml Print.ml Circuit.ml SHA1.ml Crypto.ml Interpreter.ml SecServer.ml SecServer.ml-e SMCMain.ml FFI.ml ffibridge.ml prog.ml runtime.ml interpreteriface.ml smciface.ml alice_list.txt bob_list.txt hashtable.ml intersect.txt
