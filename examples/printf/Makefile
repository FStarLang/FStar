VERFILES=
FSTAR_HOME=../..
include ../Makefile.include
include $(FSTAR_HOME)/ulib/ml/Makefile.include

all: SimplePrintf.uver

# This doesn't work because of bug #...
ocaml: SimplePrintf.fst
	mkdir -p out
	$(MAKE) -C $(ULIB_ML)
	$(FSTAR) --explicit_deps $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml SimplePrintf.fst
	$(OCAMLOPT) out/SimplePrintf.ml -o SimplePrintf.exe
	./SimplePrintf.exe

CFSTAR=$(subst CURRENT_DIR,examples/printf,$(CVERFSTAR))
all-cver: SimplePrintf.ucver

