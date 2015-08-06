ALLOCATOR_DIR = ../../runtime/allocator
ALLOCATOR_FILES = $(ALLOCATOR_DIR)/camlstack.o $(ALLOCATOR_DIR)/stack.o $(ALLOCATOR_DIR)/bitmask.o $(ALLOCATOR_DIR)/camlstack.mli

OCAML = ocamlfind ocamlc -custom -g -package batteries -linkpkg -thread -I ../../src/ocaml-output/ -I $(ALLOCATOR_DIR) $(ALLOCATOR_FILES) ../../src/ocaml-output/support.ml

Factorial.ml: factorial.fst
	fstar --codegen OCaml-experimental factorial.fst
	./revertManualMLs.sh

# make Factorial.ml should build all the remailing .ml files
factorial:  ListSet.ml Stack.ml FunctionalExtensionality.ml Set.ml Ghost.ml Heap.ml StackAndHeap.ml SST.ml SSTCombinators.ml Factorial.ml Test.ml
	$(OCAML) -o $@ $^


MD5.ml: md5.fst
	fstar MD5.fst
	./revertManualMLs.sh

md5: ListSet.ml Stack.ml FunctionalExtensionality.ml Set.ml Heap.ml Ghost.ml StackAndHeap.ml SST.ml SSTCombinators.ml MachineWord.ml Seq.ml SSTArray.ml ArrayAlgos.ml MD5Common.ml MD5.ml
	$(OCAML) -o $@ $^

Sieve.ml: sieve.fst
	fstar --codegen OCaml-experimental sieve.fst
	./revertManualMLs.sh

sieve: ListSet.ml Stack.ml FunctionalExtensionality.ml Set.ml Heap.ml Ghost.ml StackAndHeap.ml SST.ml SSTCombinators.ml Sieve.ml TestSieve.ml
	$(OCAML) -o $@ $^

support: #run this whenever the src file of cp is updated. It is tracked in git.
	cp ../../src/support/ocaml/fstar-lib/src/support.ml  ../../src/ocaml-output/

clean:
	rm *.cmi *.cmo MD5.ml Sieve.ml Factorial.ml md5 factorial sieve