FSTAR_HOME=../..
OTHERFLAGS=
include ../Makefile.include

all: uall sall

uall: test-elab intST.uver Exceptions.uver StExn.uver StExn.Handle.uver ExnSt.uver

sall:

ulib-cmxa:
	$(MAKE) -C ../../ulib/ml

test-elab: FStar.DM4F.Test.fst
	$(FSTAR) --lax $<

include $(FSTAR_HOME)/ulib/ml/Makefile.include

# This target is very concise and re-uses the variables defined in
# Makefile.include. You shouldn't need to call `cp` ever.
intST.exe: ulib-cmxa out intST.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml intST.fst
	$(OCAMLOPT) -I out out/IntST.ml -o out/IntST.exe
	./out/IntST.exe

ulib:
	$(MAKE) -C $(ULIB_ML)

clean:
	rm -rf out

out:
	mkdir -p out
