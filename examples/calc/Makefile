FSTAR_HOME=../..
EXCLUDED_FSTAR_FILES=Launch.fst Test.Math.Lemmas.fst CanonDeep.fst Poly1.fst Poly2.fst
FSTAR_FILES = $(filter-out $(EXCLUDED_FSTAR_FILES), $(wildcard *.fst))

all: verify-all

$(CACHE_DIR):
	mkdir -p $@

include ../Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))
