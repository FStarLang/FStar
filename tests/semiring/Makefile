FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

# This tests that the semiring tactic can be made into a plugin.
# We should make it so in the library and just remove this, along
# with its hacks.

.PHONY: %.native %.interpreted
.PRECIOUS: %.fst.checked %.ml %.cmxs

all: CanonCommSemiring.interpreted CanonCommSemiring.native

%.fst.checked: %.fst
	$(call msg, "CHECK", $<)
	$(FSTAR) --cache_checked_modules $*.fst

# NOTE: This is overriding the default rule in test.mk.
# If you add explicit dependencies here, it will fall back to the default rule.
$(OUTPUT_DIR)/%.ml:
	$(call msg, "EXTRACT", $<)
	$(FSTAR) --codegen Plugin --extract $* $*.fst
	cat $*.ml.fixup >> $@

%.cmxs: %.ml
	$(call msg, "OCAMLOPT", $<)
	$(OCAMLOPT) -w -8 -shared -package fstar.lib -o $@ $*.ml

# REMARK: --load will compile $*.ml if $*.cmxs does not exist, but we
# compile it before and use --load_cmxs
%.native: $(OUTPUT_DIR)/%.cmxs %.fst %.Test.fst
	$(call msg, "CHECK NATIVE", $<)
	$(FSTAR) --load_cmxs $* $*.Test.fst
	@touch $@

%.interpreted: %.fst.checked %.Test.fst
	$(call msg, "CHECK INTERP", $<)
	$(FSTAR) $*.Test.fst
	@touch $@

clean:
	rm -f *.checked *.ml *.o *.cm[ix] *.cmxs *~
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR)
