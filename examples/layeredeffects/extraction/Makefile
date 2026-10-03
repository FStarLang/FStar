FSTAR_ROOT ?= ../../..
FSTAR_EXE ?= $(FSTAR_ROOT)/stage2/out/bin/fstar.exe
FSTAR := $(abspath $(FSTAR_EXE))

# LL and MSeqExn were removed with the layered-effect examples.  InformativeIndices
# was a negative test for effect indices, which no longer exist.
FILES=ParametricST

all: $(addsuffix .cmp, $(FILES)) DM4F_layered5_cmp

accept: $(addsuffix .accept, $(FILES)) DM4F_layered5_accept

# Section 126.  Custard rather than --codegen OCaml, and --no_cmi is gone with
# it: Custard reads the implementation whether or not an interface is in the
# way (section 4.2), so asking it not to would be asking for nothing.
# Custard reads the *implementation* of every module it reaches, so every
# module has to have been checked first -- there is no extract-as-you-check
# mode.  CHECK_ARGS is that first pass.
CHECK_ARGS=--cache_checked_modules --cache_dir out/cache --warn_error -272-333-330 --include .. --admit_smt_queries true
FSTAR_ARGS=--codegen Custard --cache_dir out/cache --warn_error -272-333-330 --include .. --admit_smt_queries true

DM4F_layered5_gen: out
	$(FSTAR) $(CHECK_ARGS) ../DM4F_Utils.fst
	$(FSTAR) $(CHECK_ARGS) ../DM4F_layered5.fst
	$(FSTAR) $(FSTAR_ARGS) --custard_entry_module DM4F_layered5 \
	  ../DM4F_layered5.fst -o out/DM4F_layered5.ml
	$(FSTAR) --ocamlopt out/DM4F_layered5.ml -o out/DM4F_layered5.exe
	./out/DM4F_layered5.exe >out/DM4F_layered5.out 2>&1

DM4F_layered5_cmp: DM4F_layered5_gen
	diff -u --strip-trailing-cr DM4F_layered5.expected out/DM4F_layered5.out

DM4F_layered5_accept: DM4F_layered5_gen
	cp out/DM4F_layered5.out DM4F_layered5.expected

%.gen: %.fst out
	$(FSTAR) $(CHECK_ARGS) $<
	$(FSTAR) $(FSTAR_ARGS) --custard_entry_module $(*F) $< -o out/$(*F).ml
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
