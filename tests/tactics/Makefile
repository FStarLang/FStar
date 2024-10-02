FSTAR_HOME=../..

FSTAR_FILES=$(wildcard *.fst)

all: verify-all Hacl.Meta.Use.fst.test

include $(FSTAR_HOME)/examples/Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

clean:
	$(call msg, "CLEAN")
	$(Q)rm -f .depend
	$(Q)rm -rf _cache
	$(Q)rm -rf _output

Hacl_Meta.ml:
	$(Q)$(FSTAR) Hacl.Meta.fst --codegen Plugin

Hacl.Meta.Use.fst.test: Hacl.Meta.Use.fst Hacl_Meta.ml
	$(Q)$(FSTAR) $< --load Hacl.Meta
	@touch $@
