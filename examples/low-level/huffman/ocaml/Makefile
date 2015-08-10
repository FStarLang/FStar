ALLOCATOR_DIR = ../../../../runtime/allocator
ALLOCATOR_FILES = $(ALLOCATOR_DIR)/camlstack.o $(ALLOCATOR_DIR)/stack.o $(ALLOCATOR_DIR)/bitmask.o $(ALLOCATOR_DIR)/camlstack.mli

FLAGS=-I $(ALLOCATOR_DIR) -g
OCAMLC=ocamlfind ocamlopt 

huffman: huffman.ml huffman_ffi.o
	$(OCAMLC) $(FLAGS) -o $@ $^ $(ALLOCATOR_FILES) 

%.o: %.c
	$(OCAMLC) $(FLAGS) -c  $^ -o $@

clean: 
	$(RM) huffman *.o *.cmo *.cmi