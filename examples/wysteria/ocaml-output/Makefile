FSTAR_HOME=../../..

OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/contrib/Platform/ml $(FSTAR_HOME)/contrib/CoreCrypto/ml $(FSTAR_HOME)/lib/ml/native_int $(FSTAR_HOME)/lib/ml)

OCAMLC=ocamlfind ocamlopt -package batteries -linkpkg -g -thread

a.out:
	$(MAKE) -C $(FSTAR_HOME)/lib/ml PRIMS_DIR=native_int
	$(MAKE) -C $(FSTAR_HOME)/contrib/
	cp ../ml/ffibridge.ml .
	cp ../ml/runtime.ml .
	cp ../ml/interpreteriface.ml .
	cp ../ml/hashtable.ml .
	$(OCAMLC) $(OCAML_INCLUDE_PATHS) $(FSTAR_HOME)/lib/ml/fstarlib.cmxa \
	  $(FSTAR_HOME)/contrib/CoreCrypto/ml/CoreCrypto.cmxa \
	  FStar_List_Tot.ml FStar_OrdSet.ml FStar_OrdMap.ml FStar_Ghost.ml \
	  Prins.ml AST.ml ffibridge.ml Semantics.ml PSemantics.ml \
	  RuntimeTheory.ml runtime.ml Print.ml hashtable.ml Circuit.ml \
	  Interpreter.ml FFI.ml prog.ml interpreteriface.ml smciface.ml \
	  SMCMain.ml \
	  -o a.out
# see ../Makefile ... removed some files
	# $(OCAMLC) $(OCAML_INCLUDE_PATHS) $(FSTAR_HOME)/contrib/CoreCrypto/ml/CoreCrypto.cmxa prims.ml FStar_Ghost.ml FStar_List_Tot.ml FStar_ST.ml FStar_All.ml FStar_List.ml FStar_OrdSet.ml FStar_OrdMap.ml FStar_IO.ml FStar_String.ml  \
	#             Prins.ml AST.ml ffibridge.ml Semantics.ml PSemantics.ml RuntimeTheory.ml runtime.ml Print.ml hashtable.ml Circuit.ml SHA1.ml Crypto.ml Interpreter.ml SecServer.ml FFI.ml prog.ml interpreteriface.ml smciface.ml SMCMain.ml -o a.out

clean:
	$(MAKE) -C $(FSTAR_HOME)/lib/ml clean
	$(MAKE) -C $(FSTAR_HOME)/contrib/ clean
	rm -f *.cmi *.cmx *.o a.out circuit_* input_* output_* config* bar.txt

distclean: clean
	rm -f prims.ml FStar_Ghost.ml FStar_FunctionalExtensionality.ml FStar_List_Tot.ml FStar_Heap.ml FStar_ST.ml FStar_All.ml FStar_Seq.ml FStar_Set.ml FStar_SeqProperties.ml FStar_List.ml FStar_ListProperties.ml FStar_OrdSet.ml FStar_OrdMap.ml FStar_Classical.ml FStar_IO.ml FStar_String.ml Prins.ml AST.ml Semantics.ml PSemantics.ml RuntimeTheory.ml Platform_Bytes.ml CoreCrypto.ml Print.ml Circuit.ml SHA1.ml Crypto.ml Interpreter.ml SecServer.ml SecServer.ml-e SMCMain.ml FFI.ml ffibridge.ml runtime.ml interpreteriface.ml alice_list.txt bob_list.txt hashtable.ml intersect.txt
