FSTAR_HOME=../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
ALLOCATOR_DIR = ../../runtime/allocator
ALLOCATOR_FILES = $(ALLOCATOR_DIR)/camlstack.o $(ALLOCATOR_DIR)/stack.o \
	$(ALLOCATOR_DIR)/bitmask.o $(ALLOCATOR_DIR)/camlstack.mli

FSTAR_OCAML_LIB=prims.ml FStar_List.ml FStar_All.ml FStar_ST.ml
OCAML = ocamlfind ocamlopt -g -package batteries -linkpkg -thread -I ../../src/ocaml-output/\
 -I $(ALLOCATOR_DIR) $(ALLOCATOR_FILES) $(addprefix ../../src/ocaml-output/, $(FSTAR_OCAML_LIB))

all: codegen demo

# Those ml files are copied back from the low-level folder, same as what Abhishek
# was doing. It would be good to have extraction working so that we get the good
# files immediately
codegen: demo.fst
	$(FSTAR) $^
	cp ../low-level/Located.ml .
	cp ../low-level/Lref.ml .
	cp ../low-level/SST.ml .
	cp ../low-level/Seq.ml .
	cp ../low-level/SSTArray.ml .
	cp ./ml/CSystem.ml ./ml/CBuffer.ml ./ml/Test.ml .

SST_FILES=ListSet.ml Stack.ml FStar_FunctionalExtensionality.ml FStar_Ghost.ml Located.ml \
	Lref.ml StackAndHeap.ml SST.ml Seq.ml SSTArray.ml SSTCombinators.ml

demo: $(SST_FILES) CBuffer.ml CSystem.ml Demo.ml Test.ml
	gcc -c ./ml/cfun.c -o cfun.o
	cp ./ml/CSystem.ml ./ml/CBuffer.ml .
	$(OCAML) cfun.o -o $@ $^
	@echo "Content of the output.txt file :"
	@cat output.txt

clean:
	rm -f *.ml *.cmi *.cmo *.cmx *.o || true
