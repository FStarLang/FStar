VERFILES=printf.fst
FSTAR_HOME=../..
include ../Makefile.include

FSTAR_HOME=../..
include $(FSTAR_HOME)/ulib/ml/Makefile.include

all: uall sall

uall: SimplePrintf.uver

sall: .all.ver

ocaml: SimplePrintf.fst
	$(MAKE) -C $(ULIB_ML)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml SimplePrintf.fst
	$(OCAMLOPT) out/SimplePrintf.ml -o SimplePrintf.exe
	./SimplePrintf.exe
