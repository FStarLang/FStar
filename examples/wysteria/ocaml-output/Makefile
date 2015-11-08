OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g -w -8

FSTAR_HOME=../../..

a.out:
	make -C .. codegen
	cp $(FSTAR_HOME)/lib/ml/native_int/prims.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_ST.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_All.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_IO.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_List.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_String.ml .
	cp $(FSTAR_HOME)/contrib/Platform/ml/platform.ml .
	cp ../ml/ffibridge.ml .
	cp ../ml/runtime.ml .
	cp ../ml/prog.ml .
	$(OCAMLOPT) prims.ml FStar_Ghost.ml FStar_List_Tot.ml FStar_ST.ml FStar_All.ml FStar_List.ml FStar_OrdSet.ml FStar_OrdMap.ml FStar_IO.ml FStar_String.ml  \
	            Prins.ml AST.ml ffibridge.ml Semantics.ml platform.ml runtime.ml Print.ml Circuit.ml Interpreter.ml SecServer.ml FFI.ml prog.ml Main.ml -o a.out

clean:
	rm -f *.cmi *.cmx *.o a.out circuit_* input_* output_* config* bar.txt

distclean: clean
	rm -f prims.ml FStar_Ghost.ml FStar_FunctionalExtensionality.ml FStar_List_Tot.ml FStar_Heap.ml FStar_ST.ml FStar_All.ml FStar_List.ml FStar_ListProperties.ml FStar_OrdSet.ml FStar_OrdMap.ml FStar_Classical.ml FStar_IO.ml FStar_String.ml Prins.ml AST.ml Semantics.ml Print.ml Circuit.ml Interpreter.ml SecServer.ml SecServer.ml-e Main.ml FFI.ml ffibridge.ml prog.ml runtime.ml
