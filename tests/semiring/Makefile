FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

# This tests that the semiring tactic can be made into a plugin.
# We should make it so in the library and just remove this, along
# with its hacks.

all: $(OUTPUT_DIR)/CanonCommSemiring.interpreted $(OUTPUT_DIR)/CanonCommSemiring.native

# NOTE: This is overriding the default rule in test.mk.
# If you add explicit dependencies here, it will fall back to the default rule.
$(OUTPUT_DIR)/%.ml:
	$(call msg, "EXTRACT", $<)
	$(FSTAR) --codegen Plugin --extract $* $*.fst
	cat $*.ml.fixup >> $@

$(OUTPUT_DIR)/%.cmxs: $(OUTPUT_DIR)/%.ml
	$(call msg, "OCAMLOPT", $<)
	$(FSTAR_EXE) --ocamlopt_plugin -o $@ $<

# REMARK: --load will compile $*.ml if $*.cmxs does not exist, but we
# compile it before and use --load_cmxs
$(OUTPUT_DIR)/%.native: $(OUTPUT_DIR)/%.cmxs %.fst %.Test.fst
	$(call msg, "CHECK NATIVE", $<)
	$(FSTAR) --load_cmxs $* $*.Test.fst
	@touch $@

$(OUTPUT_DIR)/%.interpreted: $(CACHE_DIR)/%.fst.checked %.Test.fst
	$(call msg, "CHECK INTERP", $<)
	$(FSTAR) $*.Test.fst
	@touch $@
