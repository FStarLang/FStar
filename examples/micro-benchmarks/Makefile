FSTAR_HOME=../..

FSTAR_FILES=$(wildcard *.fst)
# FSTAR_FILES+= Coercions1Phase.fst

all: verify-all

include ../Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES))) \
            Erasable.ml-cmp \
            $(CACHE_DIR)/Coercions1Phase.fst.checked

$(CACHE_DIR)/MustEraseForExtraction.fst.checked: OTHERFLAGS += --warn_error @318

$(CACHE_DIR)/Coercions1Phase.fst.checked: OTHERFLAGS += --use_two_phase_tc false
$(CACHE_DIR)/Coercions1Phase.fst.checked: Coercions1Phase.fst

Coercions1Phase.fst: Coercions.fst
	sed 's/module Coercions/module Coercions1Phase/' < $< > $@

Erasable.ml: Erasable.fst
	$(FSTAR) --codegen OCaml --extract Erasable $^

Erasable.ml-cmp: Erasable.ml Erasable.ml.expected
	diff --strip-trailing-cr $< $<.expected
