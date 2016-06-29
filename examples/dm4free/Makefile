FSTAR_HOME=../..
OTHERFLAGS=
include ../Makefile.include

all: uall

uall: NewPrims.uver

%.uver: %.fst
	$(FSTAR) --universes --verify_module $* $^


include $(FSTAR_HOME)/ulib/ml/Makefile.include

# This target is very concise and re-uses the variables defined in
# Makefile.include. You shouldn't need to call `cp` ever.
intST.test: out intST.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --universes intST.fst
	$(OCAMLOPT) -I out out/IntST.ml -o out/IntST.exe
	./out/IntST.exe

ulib:
	$(MAKE) -C $(ULIB_ML)

clean:
	rm -rf out

out:
	mkdir -p out
