FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

all: Hacl.Meta.Use.fst.test

# TacTest exercises reification of the Tac effect during extraction.
all: $(OUTPUT_DIR)/TacTest.ml

$(OUTPUT_DIR)/TacTest.ml: $(CACHE_DIR)/TacTest.fst.checked
	$(call msg, "EXTRACT", TacTest.fst)
	$(FSTAR) TacTest.fst --codegen Plugin --odir $(OUTPUT_DIR)

Hacl_Meta.ml: $(CACHE_DIR)/Hacl.Meta.fst.checked
	$(FSTAR) Hacl.Meta.fst --codegen Plugin

Hacl.Meta.Use.fst.test: Hacl.Meta.Use.fst Hacl_Meta.ml
	$(FSTAR) $< --load Hacl.Meta
	touch $@

$(OUTPUT_DIR)/Postprocess.fst.output: FSTAR_ARGS+=--dump_module Postprocess --ugly
