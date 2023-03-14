include ../../Makefile.include

include $(FSTAR_ULIB)/ml/Makefile.include

all: ../HoareST.cmp ParametricST.cmp InformativeIndices.errcmp

accept: ../HoareST.accept ParametricST.accept InformativeIndices.erraccept

FSTAR_ARGS=$(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --warn_error -333-330

%.gen: %.fst out
	$(FSTAR) $(FSTAR_ARGS) --extract $(*F) $<
	$(OCAMLOPT) out/$(*F).ml -o out/$(*F).exe
	./out/$(*F).exe >out/$(*F).out 2>&1

%.cmp: %.gen
	diff -u --strip-trailing-cr $(*F).expected out/$(*F).out

%.accept: %.gen
	cp out/$(*F).out $(*F).expected

%.errgen: %.fst out
	-$(FSTAR) $(FSTAR_ARGS) --extract $(*F) $< >out/$(*F).err 2>&1

%.errcmp: %.errgen
	diff -u --strip-trailing-cr $(*F).expected out/$(*F).err

%.erraccept: %.errgen
	cp out/$(*F).err $(*F).expected

out:
	mkdir -p out

clean:
	rm -rf out *~
