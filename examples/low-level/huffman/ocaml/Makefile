ALLOCATOR_DIR = ../../../../runtime/allocator
ALLOCATOR_FILES = $(ALLOCATOR_DIR)/camlstack.o $(ALLOCATOR_DIR)/stack.o $(ALLOCATOR_DIR)/bitmask.o $(ALLOCATOR_DIR)/camlstack.mli

OCAML = ocamlfind ocamlc -custom -g -package batteries -linkpkg -thread -I ../../../../src/ocaml-output/ -I $(ALLOCATOR_DIR) $(ALLOCATOR_FILES) ../../../../src/ocaml-output/support.ml

huffman: huffman.ml
	$(OCAML) -o $@ $^

shuffman: shuffman.ml
	$(OCAML) -o $@ $^
