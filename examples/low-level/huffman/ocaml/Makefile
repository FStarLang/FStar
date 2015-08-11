ifdef WINDIR
EXE=.exe
else
EXE=
endif

ALLOCATOR_DIR = ../../../../runtime/allocator
ALLOCATOR_FILES = $(ALLOCATOR_DIR)/camlstack.o $(ALLOCATOR_DIR)/stack.o $(ALLOCATOR_DIR)/bitmask.o $(ALLOCATOR_DIR)/camlstack.mli

OPT_FLAGS=-strict-sequence -w @1..2+3@8@10..12@14..21@23..40-41@43
FLAGS=-I $(ALLOCATOR_DIR) -g $(OPT_FLAGS)
OCAMLC=ocamlfind ocamlopt 

huffman$(EXE): huffman.ml huffman_ffi.o
	$(OCAMLC) $(FLAGS) -o $@ $^ $(ALLOCATOR_FILES) 

%.o: %.c
	$(OCAMLC) $(FLAGS) -c  $^ -o $@

clean: 
	$(RM) huffman$(EXE) *.o *.cm*
