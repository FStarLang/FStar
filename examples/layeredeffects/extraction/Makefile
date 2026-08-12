FSTAR_ROOT ?= ../../..
FSTAR_EXE ?= $(FSTAR_ROOT)/stage2/out/bin/fstar.exe
FSTAR := $(abspath $(FSTAR_EXE))

# LL and MSeqExn were removed with the layered-effect examples.  InformativeIndices
# was a negative test for effect indices, which no longer exist.
FILES=ParametricST

all: $(addsuffix .cmp, $(FILES)) DM4F_layered5_cmp

accept: $(addsuffix .accept, $(FILES)) DM4F_layered5_accept

FSTAR_ARGS=--odir out --codegen OCaml --no_cmi --warn_error -272-333-330 --include .. --admit_smt_queries true

DM4F_layered5_gen: out
	$(FSTAR) $(FSTAR_ARGS) --extract 'DM4F_layered5' ../DM4F_layered5.fst
	$(FSTAR) --ocamlopt out/DM4F_layered5.ml -o out/DM4F_layered5.exe
	./out/DM4F_layered5.exe >out/DM4F_layered5.out 2>&1

DM4F_layered5_cmp: DM4F_layered5_gen
	diff -u --strip-trailing-cr DM4F_layered5.expected out/DM4F_layered5.out

DM4F_layered5_accept: DM4F_layered5_gen
	cp out/DM4F_layered5.out DM4F_layered5.expected

%.gen: %.fst out
	$(FSTAR) $(FSTAR_ARGS) --extract $(*F) $<
	$(FSTAR) --ocamlopt out/$(*F).ml -o out/$(*F).exe
	./out/$(*F).exe >out/$(*F).out 2>&1

%.cmp: %.gen
	diff -u --strip-trailing-cr $(*F).expected out/$(*F).out

%.accept: %.gen
	cp out/$(*F).out $(*F).expected

out:
	mkdir -p out

clean:
	rm -rf out *~
