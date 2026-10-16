FSTAR_ROOT ?= ../../..

include $(FSTAR_ROOT)/mk/test.mk

# Test for `--ext no_krml_private`.
#
# When a module has an interface, the definitions the interface does not
# declare are private to the module, and the typechecker tags them with the
# internal `KrmlPrivate` attribute so that they are emitted as `static` C
# functions (see [mark_karamel_private] in FStarC.TypeChecker.Tc).
#
# `--ext no_krml_private` disables that tagging. Here, KrmlPrivateTest.fsti
# only declares `exposed`, so, on Custard's C backend:
#
#   - by default, `hidden` is emitted as a `static` function and does not
#     appear in the header;
#   - with `--ext no_krml_private`, it is emitted as a normal, externally
#     visible function and is declared in the header.
#
# NB: the flag is consumed at typechecking time, so each variant needs its
# own cache directory.

all: $(OUTPUT_DIR)/private.checked $(OUTPUT_DIR)/nonprivate.checked

# $(1) = variant name, $(2) = extra F* flags
define c_variant
$(OUTPUT_DIR)/$(1)/KrmlPrivateTest.c: KrmlPrivateTest.fsti KrmlPrivateTest.fst $(FSTAR_EXE)
	$$(call msg, "EXTRACT", "KrmlPrivateTest ($(1))")
	$$(Q)rm -rf $(OUTPUT_DIR)/$(1) && mkdir -p $(OUTPUT_DIR)/$(1)
	$$(Q)$$(FSTAR_EXE) $$(SIL) $(2) --cache_checked_modules \
	  --odir $(OUTPUT_DIR)/$(1) --cache_dir $(OUTPUT_DIR)/$(1) KrmlPrivateTest.fsti
	$$(Q)$$(FSTAR_EXE) $$(SIL) $(2) --cache_checked_modules \
	  --odir $(OUTPUT_DIR)/$(1) --cache_dir $(OUTPUT_DIR)/$(1) KrmlPrivateTest.fst
	$$(Q)$$(FSTAR_EXE) $$(SIL) $(2) --codegen C \
	  --custard_entry_module KrmlPrivateTest \
	  --cache_dir $(OUTPUT_DIR)/$(1) -o $$@ \
	  $(OUTPUT_DIR)/$(1)/KrmlPrivateTest.fst.checked
endef

$(eval $(call c_variant,private,))
$(eval $(call c_variant,nonprivate,--ext no_krml_private))

$(OUTPUT_DIR)/private.checked: $(OUTPUT_DIR)/private/KrmlPrivateTest.c
	$(call msg, "CHECK", "hidden is static")
	$(Q)grep -q '^static uint32_t KrmlPrivateTest_hidden(' $<
	$(Q)! grep -q 'KrmlPrivateTest_hidden' $(OUTPUT_DIR)/private/KrmlPrivateTest.h
	$(Q)touch $@

$(OUTPUT_DIR)/nonprivate.checked: $(OUTPUT_DIR)/nonprivate/KrmlPrivateTest.c
	$(call msg, "CHECK", "hidden is public")
	$(Q)! grep -q '^static uint32_t KrmlPrivateTest_hidden(' $<
	$(Q)grep -q '^uint32_t KrmlPrivateTest_hidden(' $<
	$(Q)grep -q 'KrmlPrivateTest_hidden' $(OUTPUT_DIR)/nonprivate/KrmlPrivateTest.h
	$(Q)touch $@
