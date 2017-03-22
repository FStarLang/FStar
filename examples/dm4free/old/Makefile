FSTAR_HOME=../../..
include ../../Makefile.include

all: uall
uall: intST.uver Exceptions.uver-explicit ExceptionsWithState.uver StExn.uver-explicit StExn.Handle.uver-explicit

%.uver-explicit: %.fst
	$(FSTAR) $^ --explicit_deps

%.uver: %.fst
	$(FSTAR) $^

include $(FSTAR_HOME)/ulib/ml/Makefile.include

# This target is very concise and re-uses the variables defined in
# Makefile.include. You shouldn't need to call `cp` ever.
intST.exe: ulib-cmxa out intST.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml intST.fst
	$(OCAMLOPT) -I out out/IntST.ml -o out/IntST.exe
	./out/IntST.exe

ulib:
	$(MAKE) -C $(ULIB_ML)

ulib-cmxa:
	$(MAKE) -C ../../../ulib/ml

clean:
	rm -rf out

out:
	mkdir -p out
