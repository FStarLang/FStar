FSTAR_HOME=../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
ALLOCATOR_DIR = ../../runtime/allocator
ALLOCATOR_FILES = $(ALLOCATOR_DIR)/camlstack.o $(ALLOCATOR_DIR)/stack.o $(ALLOCATOR_DIR)/bitmask.o $(ALLOCATOR_DIR)/camlstack.mli

OCAML = ocamlfind ocamlopt -g -package batteries -linkpkg -thread -I ../../src/ocaml-output/ -I $(ALLOCATOR_DIR) $(ALLOCATOR_FILES) ../../src/ocaml-output/support.ml ./ml/cfun.o

Demo.ml: demo.fst
	$(FSTAR) $^
	cp ../low-level/Located.ml .
	cp ../low-level/Lref.ml .
	cp ../low-level/SST.ml .
	cp ../low-level/Seq.ml .
	cp ../low-level/SSTArray.ml .
	cp ./ml/CSystem.ml ./ml/CBuffer.ml .

SST_FILES=ListSet.ml Stack.ml FunctionalExtensionality.ml Ghost.ml Located.ml \
	Lref.ml StackAndHeap.ml SST.ml Seq.ml SSTArray.ml SSTCombinators.ml

demo: $(SST_FILES) CBuffer.ml CSystem.ml Demo.ml Test.ml
	cp ./ml/CSystem.ml ./ml/CBuffer.ml .
	$(OCAML) -o $@ $^

clean:
	rm Demo.ml
