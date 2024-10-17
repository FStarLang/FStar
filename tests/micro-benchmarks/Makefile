FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

OTHERFLAGS+=--warn_error +240

all: verify-all \
	ns-resolution \
	Erasable.ml-cmp \
	InlineForExtractionNormRequest.ml-cmp \
	MachineIntegerConstants.ml-cmp \
	ExtractMutRecTypesAndTerms.ml-cmp

ns-resolution:
	+$(MAKE) -C ns_resolution all

$(CACHE_DIR)/MustEraseForExtraction.fst.checked: OTHERFLAGS += --warn_error @318

%.ml: %.fst
	$(FSTAR) $(OTHERFLAGS) --codegen OCaml --odir . --extract $(subst .ml,, $@) $^

%.ml-cmp: %.ml %.ml.expected
	diff -u --strip-trailing-cr $<.expected $<
	touch $@

.PRECIOUS: %.ml
