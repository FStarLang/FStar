ALLOCATOR_DIR = ../../../../runtime/allocator
ALLOCATOR_FILES = $(ALLOCATOR_DIR)/camlstack.o $(ALLOCATOR_DIR)/stack.o $(ALLOCATOR_DIR)/bitmask.o $(ALLOCATOR_DIR)/camlstack.mli

OCAMLC = ocamlfind ocamlc -custom -g -I $(ALLOCATOR_DIR) 

huffman: huffman.ml huffman_ffi.o
	$(OCAMLC) -o $@ $^ $(ALLOCATOR_FILES) 

%.o: %.c
	$(OCAMLC) -g -c  $^ -o $@

clean: 
	$(RM) huffman *.o *.cmo *.cmi