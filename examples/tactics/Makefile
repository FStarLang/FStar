FSTAR_HOME=../..
KREMLIN_HOME?=$(FSTAR_HOME)/../Kremlin
INCLUDE_PATHS=$(KREMLIN_HOME)/kremlib
EXCLUDED_FSTAR_FILES=Launch.fst CanonCommSemiring.fst \
		     Test.Math.Lemmas.fst CanonDeep.fst
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

clean_imp_native:
	rm -f ../native_tactics/Registers_List.ml ../native_tactics/Registers.List.ml ../native_tactics/Registers_List.cmxs

imp_native: Imp.fst ../native_tactics/Registers.List.fst
	$(MAKE) -C ../native_tactics Registers.List.ml
	$(FSTAR) Imp.fst --include ../native_tactics/ --load Registers.List --warn_error -266

imp: Imp.fst ../native_tactics Registers.List.ml
	$(FSTAR) Imp.fst --include ../native_tactics/
