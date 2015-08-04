all:
	ocamlfind ocamlc -o program -package batteries -linkpkg -thread -I ../../src/ocaml-output/ ../../src/ocaml-output/support.ml ListSet.ml Stack.ml FunctionalExtensionality.ml Set.ml Heap.ml Ghost.ml StackAndHeap.ml SST.ml SSTCombinators.ml Factorial.ml Test.ml



MD5:
	fstar MD5.fst
	ocamlfind ocamlc -o program -package batteries -linkpkg -thread -I ../../src/ocaml-output/ ../../src/ocaml-output/support.ml ListSet.ml Stack.ml FunctionalExtensionality.ml Set.ml Heap.ml Ghost.ml StackAndHeap.ml SST.ml SSTCombinators.ml MachineWord.ml Seq.ml Array.ml ArrayAlgos.ml MD5.ml
