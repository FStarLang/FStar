ifdef WINDIR
EXE=.exe
else
EXE=
endif

ALLOCATOR_DIR = ../../../../runtime/allocator
ALLOCATOR_FILES = $(ALLOCATOR_DIR)/camlstack.o $(ALLOCATOR_DIR)/stack.o $(ALLOCATOR_DIR)/bitmask.o $(ALLOCATOR_DIR)/camlstack.mli

FLAGS=-I $(ALLOCATOR_DIR) -g
# OCAMLC=ocamlfind ocamlc
# OCAMLLINK=ocamlfind ocamlc -custom
OCAMLC=ocamlfind ocamlopt
OCAMLLINK=ocamlfind ocamlopt
CMO=cmx

all: allocator huffman$(EXE)

huffman$(EXE): huffman.ml huffman_ffi.o
	$(OCAMLLINK) $(FLAGS) -o $@ $^ $(ALLOCATOR_FILES)

allocator:
	$(MAKE) OCAMLC="$(OCAMLC)" CMO=$(CMO) OCAMLLINK="$(OCAMLLINK)" -C $(ALLOCATOR_DIR)

%.o: %.c
	$(OCAMLC) $(FLAGS) -c  $^ -o $@

clean:
	$(MAKE) -C $(ALLOCATOR_DIR) clean
	$(RM) huffman$(EXE) *.o *.cm*
