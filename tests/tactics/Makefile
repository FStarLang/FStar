FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

all: Hacl.Meta.Use.fst.test

# The negative tests in this file may succeed with hints, force them off.
$(CACHE_DIR)/Pruning.fst.checked: HINTS_ENABLED=

Hacl_Meta.ml: $(CACHE_DIR)/Hacl.Meta.fst.checked
	$(FSTAR) Hacl.Meta.fst --codegen Plugin

Hacl.Meta.Use.fst.test: Hacl.Meta.Use.fst Hacl_Meta.ml
	$(FSTAR) $< --load Hacl.Meta
	touch $@

$(OUTPUT_DIR)/Postprocess.fst.output: FSTAR_ARGS+=--dump_module Postprocess --ugly
