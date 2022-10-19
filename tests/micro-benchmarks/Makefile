FSTAR_HOME=../..

FSTAR_FILES = $(wildcard *.fst)

# This consumes too much memory (8GB), so disable it for now.
FSTAR_FILES := $(filter-out SteelIntroExists.fst, $(FSTAR_FILES))

all: verify-all ns-resolution

ns-resolution:
	+$(MAKE) -C ns_resolution

include $(FSTAR_HOME)/examples/Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES))) \
            Erasable.ml-cmp \
	    InlineForExtractionNormRequest.ml-cmp \
	    MachineIntegerConstants.ml-cmp \
	    ExtractMutRecTypesAndTerms.ml-cmp

$(CACHE_DIR)/MustEraseForExtraction.fst.checked: OTHERFLAGS += --warn_error @318

%.ml: %.fst
	$(FSTAR) --codegen OCaml --extract $(subst .ml,, $@) $^

%.ml-cmp: %.ml %.ml.expected
	diff -u --strip-trailing-cr $< $<.expected


clean:
	rm -f .depend
	rm -rf _cache
	rm -rf _output
