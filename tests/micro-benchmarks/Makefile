FSTAR_HOME=../..
OTHERFLAGS+=--warn_error +240
FSTAR_FILES = $(wildcard *.fst)

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
	$(FSTAR) $(OTHERFLAGS) --codegen OCaml --extract $(subst .ml,, $@) $^

%.ml-cmp: %.ml %.ml.expected
	diff -u --strip-trailing-cr $<.expected $<
	touch $@

clean:
	rm -f .depend
	rm -rf _cache
	rm -rf _output

.PRECIOUS: %.ml
