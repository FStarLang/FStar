FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

all: Hacl.Meta.Use.fst.test

# The negative tests in this file may succeed with hints, force them off.
$(CACHE_DIR)/Pruning.fst.checked: HINTS_ENABLED=

Hacl_Meta.ml:
	$(FSTAR) Hacl.Meta.fst --codegen Plugin

Hacl.Meta.Use.fst.test: Hacl.Meta.Use.fst Hacl_Meta.ml
	$(FSTAR) $< --load Hacl.Meta
	touch $@
