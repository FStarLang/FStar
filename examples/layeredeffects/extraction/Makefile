include ../../Makefile.include

include $(FSTAR_ULIB)/ml/Makefile.include

all: ParametricST.cmp InformativeIndices.errcmp

accept: ParametricST.accept InformativeIndices.erraccept

FSTAR_ARGS=$(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --warn_error -333-330

%.gen: %.fst
	$(FSTAR) $(FSTAR_ARGS) --extract $* $<
	$(OCAMLOPT) out/$*.ml -o out/$*.exe
	./out/$*.exe >out/$*.out 2>&1

%.errgen: %.fst
	-$(FSTAR) $(FSTAR_ARGS) --extract $* $< > out/$*.err 2>&1

%.errcmp: %.errgen
	diff -u --strip-trailing-cr $*.expected out/$*.err

%.cmp: %.gen
	diff -u --strip-trailing-cr $*.expected out/$*.out

%.accept: %.gen
	cp out/$*.out $*.expected

%.erraccept: %.errgen
	cp out/$*.err $*.expected

parametricst: out ParametricST.cmp

out:
	mkdir -p out

clean:
	rm -rf out *~
