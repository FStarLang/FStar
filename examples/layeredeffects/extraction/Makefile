include ../../Makefile.include

include $(FSTAR_ULIB)/ml/Makefile.include

FILES=../LL ../HoareST ParametricST

all: $(addsuffix .cmp, $(FILES)) DM4F_layered5_cmp #InformativeIndices.errcmp

accept: $(addsuffix .accept, $(FILES)) DM4F_layered5_accept #InformativeIndices.erraccept

FSTAR_ARGS=$(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --warn_error -272-333-330 --include .. --admit_smt_queries true

DM4F_layered5_gen:
	$(FSTAR) $(FSTAR_ARGS) --extract 'ID5 DM4F_layered5' ../DM4F_layered5.fst
	$(OCAMLOPT) -I out out/ID5.ml out/DM4F_layered5.ml -o out/DM4F_layered5.exe
	./out/DM4F_layered5.exe >out/DM4F_layered5.out 2>&1

DM4F_layered5_cmp: DM4F_layered5_gen
	diff -u --strip-trailing-cr DM4F_layered5.expected out/DM4F_layered5.out

DM4F_layered5_accept: DM4F_layered5_gen
	cp out/DM4F_layered5.out DM4F_layered5.expected

%.gen: %.fst out
	$(FSTAR) $(FSTAR_ARGS) --extract $(*F) $<
	$(OCAMLOPT) out/$(*F).ml -o out/$(*F).exe
	./out/$(*F).exe >out/$(*F).out 2>&1

%.cmp: %.gen
	diff -u --strip-trailing-cr $(*F).expected out/$(*F).out

%.accept: %.gen
	cp out/$(*F).out $(*F).expected

%.errgen: %.fst out
	$(FSTAR) $(FSTAR_ARGS) --extract $(*F) $< >out/$(*F).err 2>&1

%.errcmp: %.errgen
	diff -u --strip-trailing-cr $(*F).expected out/$(*F).err

%.erraccept: %.errgen
	cp out/$(*F).err $(*F).expected

out:
	mkdir -p out

clean:
	rm -rf out *~
