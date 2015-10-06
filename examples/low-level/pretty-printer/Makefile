ifdef WINDIR
EXE=.exe
else
EXE=
endif

ALLOCATOR_DIR = ../../../runtime/allocator
ALLOCATOR_FILES = $(ALLOCATOR_DIR)/camlstack.o $(ALLOCATOR_DIR)/stack.o $(ALLOCATOR_DIR)/bitmask.o $(ALLOCATOR_DIR)/camlstack.mli

OPT_FLAGS=-strict-sequence -w @1..2+3@8@10..12@14..21@23..40-41@43
FLAGS=-I $(ALLOCATOR_DIR) -g -ccopt -g $(OPT_FLAGS)
OCAMLC=ocamlfind ocamlopt
OCAMLLINK=ocamlfind ocamlopt
CMO=cmx

all: allocator prettyPrinter$(EXE)

prettyPrinter$(EXE): prettyPrinter.$(CMO)
	$(OCAMLLINK) -o $@ $^ $(ALLOCATOR_FILES)

allocator:
ifdef NOGC
	$(MAKE) OCAMLC="$(OCAMLC)" CMO=$(CMO) OCAMLLINK="$(OCAMLLINK)" NOGC=y -C $(ALLOCATOR_DIR)
else
	$(MAKE) OCAMLC="$(OCAMLC)" CMO=$(CMO) OCAMLLINK="$(OCAMLLINK)" -C $(ALLOCATOR_DIR)
endif

%.$(CMO): %.ml
	$(OCAMLC) $(FLAGS) -c  $< -o $@

%.o: %.c
	$(OCAMLC) $(FLAGS) -c  $^ -o $@

clean:
	$(MAKE) -C $(ALLOCATOR_DIR) clean
	$(RM) prettyPrinter$(EXE) *.o *.cm*
