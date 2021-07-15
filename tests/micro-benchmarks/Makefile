FSTAR_HOME=../..

FSTAR_FILES=$(wildcard *.fst)
# FSTAR_FILES+= Coercions1Phase.fst

all: verify-all ns-resolution

ns-resolution:
	+$(MAKE) -C ns_resolution

include $(FSTAR_HOME)/examples/Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES))) \
            Erasable.ml-cmp \
	    InlineForExtractionNormRequest.ml-cmp \
	    MachineIntegerConstants.ml-cmp \
            $(CACHE_DIR)/Coercions1Phase.fst.checked

$(CACHE_DIR)/MustEraseForExtraction.fst.checked: OTHERFLAGS += --warn_error @318

$(CACHE_DIR)/Coercions1Phase.fst.checked: OTHERFLAGS +=
$(CACHE_DIR)/Coercions1Phase.fst.checked: Coercions1Phase.fst

Coercions1Phase.fst: Coercions.fst
	sed 's/module Coercions/module Coercions1Phase/' < $< > $@

%.ml: %.fst
	$(FSTAR) --codegen OCaml --extract $(subst .ml,, $@) $^

%.ml-cmp: %.ml %.ml.expected
	diff -u --strip-trailing-cr $< $<.expected


clean:
	rm -f .depend
	rm -rf _cache
	rm -rf _output
