ALLOCATOR_DIR = ../../runtime/allocator
ALLOCATOR_FILES=$(ALLOCATOR_DIR)/camlstack.o $(ALLOCATOR_DIR)/stack.o $(ALLOCATOR_DIR)/bitmask.o $(ALLOCATOR_DIR)/camlstack.mli

Factorial.ml: factorial.fst
	fstar --codegen OCaml-experimental factorial.fst
	./revertManualMLs.sh

factorial: Factorial.ml
	ocamlfind ocamlc -custom -g -o factorial -package batteries -linkpkg -thread -I ../../src/ocaml-output/ -I $(ALLOCATOR_DIR) $(ALLOCATOR_FILES) ../../src/ocaml-output/support.ml ListSet.ml Stack.ml FunctionalExtensionality.ml Set.ml Ghost.ml Heap.ml StackAndHeap.ml SST.ml SSTCombinators.ml Factorial.ml Test.ml

MD5.ml: md5.fst
	fstar MD5.fst
	./revertManualMLs.sh

md5: MD5.ml
	ocamlfind ocamlc -o md5 -package batteries -linkpkg -thread -I ../../src/ocaml-output/ ../../src/ocaml-output/support.ml ListSet.ml Stack.ml FunctionalExtensionality.ml Set.ml Heap.ml Ghost.ml StackAndHeap.ml SST.ml SSTCombinators.ml MachineWord.ml Seq.ml SSTArray.ml ArrayAlgos.ml MD5Common.ml MD5.ml

Sieve.ml: sieve.fst
	fstar --codegen OCaml-experimental sieve.fst
	./revertManualMLs.sh

sieve: Sieve.ml
	ocamlfind ocamlc -o sieve -package batteries -linkpkg -thread -I ../../src/ocaml-output/ ../../src/ocaml-output/support.ml ListSet.ml Stack.ml FunctionalExtensionality.ml Set.ml Heap.ml Ghost.ml StackAndHeap.ml SST.ml SSTCombinators.ml Sieve.ml TestSieve.ml

support: #run this whenever the src file of cp is updated. It is tracked in git.
	cp ../../src/support/ocaml/fstar-lib/src/support.ml  ../../src/ocaml-output/

clean:
	rm *.cmi *.cmo MD5.ml Sieve.ml Factorial.ml md5 factorial sieve