FSTAR_HOME=../..
OTHERFLAGS=
include ../Makefile.include

all: FStar.DM4F.IntST.uver FStar.DM4F.Exceptions.uver stexn.uver stexn.handle.uver exnst.uver old

# we retain these "hand-written" versions just for reference
old: intST.uver Exceptions.uver

ulib-cmxa:
	$(MAKE) -C ../../ulib/ml

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

clean:
	rm -rf out

out:
	mkdir -p out
