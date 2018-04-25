FSTAR_HOME=../..
KREMLIN_HOME?=$(FSTAR_HOME)/../Kremlin
INCLUDE_PATHS=$(KREMLIN_HOME)/kremlib
EXCLUDED_FSTAR_FILES=Launch.fst CanonCommSemiring.fst WeakVsHNF.fst \
		     Test.Math.Lemmas.fst CanonDeep.fst
FSTAR_FILES = $(filter-out $(EXCLUDED_FSTAR_FILES), $(wildcard *.fst))

all:
	mkdir -p $(CACHE_DIR)
	$(MAKE) verify-all negative-tests stringprintertest

include ../Makefile.common

verify-all: $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

launch: Launch.fst
	$(FSTAR) --unsafe_tactic_exec $^

negative-tests:
	$(MAKE) -C neg

ifdef KREMLIN_HOME
stringprintertest:
	 [ ! -f $(KREMLIN_HOME)/krml ] || [ ! -x $(KREMLIN_HOME)/krml ] || $(KREMLIN_HOME)/krml -tmpdir stringprintertest -bundle 'StringPrinter.\*' -bundle StringPrinterTest.Aux -drop 'FStar.Tactics.\*' -drop 'FStar.Reflection.\*' StringPrinterTest.fst -skip-linking
else
stringprintertest:
endif
