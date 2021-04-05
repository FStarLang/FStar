VERFILES=
include ../Makefile.include
include $(FSTAR_ULIB)/ml/Makefile.include

all: SimplePrintf.uver

# This doesn't work because of bug #...
ocaml: SimplePrintf.fst
	mkdir -p out
	$(FSTAR) --explicit_deps $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml SimplePrintf.fst
	$(OCAMLOPT) out/SimplePrintf.ml -o SimplePrintf.exe
	./SimplePrintf.exe
