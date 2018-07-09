FSTAR_HOME=../..
KREMLIN_HOME?=$(FSTAR_HOME)/../Kremlin
INCLUDE_PATHS=$(KREMLIN_HOME)/kremlib
EXCLUDED_FSTAR_FILES=Launch.fst Test.Math.Lemmas.fst CanonDeep.fst
FSTAR_FILES = $(filter-out $(EXCLUDED_FSTAR_FILES), $(wildcard *.fst))

all: verify-all #stringprintertest

$(CACHE_DIR):
	mkdir -p $@

include ../Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

launch: Launch.fst
	$(FSTAR) --unsafe_tactic_exec $^

ifdef KREMLIN_HOME
stringprintertest: $(CACHE_DIR)
	 [ ! -f $(KREMLIN_HOME)/krml ] || [ ! -x $(KREMLIN_HOME)/krml ] || $(KREMLIN_HOME)/krml -tmpdir stringprintertest -bundle 'StringPrinter.\*' -bundle StringPrinterTest.Aux -drop 'FStar.Tactics.\*' -drop 'FStar.Reflection.\*' StringPrinterTest.fst -skip-linking
else
stringprintertest:
endif

canon-native:
	$(FSTAR) --cache_checked_modules --codegen Plugin --extract 'CanonCommSemiring CanonCommMonoid CanonCommSwaps' CanonCommSemiring.fst
	rm -f ./*.cmxs
	cat CanonCommMonoid.ml.fixup >> CanonCommMonoid.ml
	cat CanonCommSemiring.ml.fixup >> CanonCommSemiring.ml
	env OCAMLPATH="../../bin/" ocamlfind ocamlopt -shared -I . -package fstar-tactics-lib -o ./CanonCommMonoid.cmxs ./CanonCommSwaps.ml ./CanonCommMonoid.ml
	env OCAMLPATH="../../bin/" ocamlfind ocamlopt -shared -I . -package fstar-tactics-lib -o ./CanonCommSemiring.cmxs ./CanonCommSwaps.ml ./CanonCommMonoid.ml ./CanonCommSemiring.ml
	$(FSTAR) --load CanonCommMonoid CanonCommMonoid.fst
	$(FSTAR) --load CanonCommSemiring CanonCommSemiring.fst
