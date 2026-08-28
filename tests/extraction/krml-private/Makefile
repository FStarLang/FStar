FSTAR_ROOT ?= ../../..

include $(FSTAR_ROOT)/mk/test.mk

# Test for `--ext no_krml_private`.
#
# When a module has an interface, the definitions the interface does not
# declare are private to the module, and the typechecker tags them with the
# internal `KrmlPrivate` attribute so that Karamel emits them as `static` C
# functions (see [mark_karamel_private] in FStarC.TypeChecker.Tc).
#
# `--ext no_krml_private` disables that tagging. Here, KrmlPrivateTest.fsti
# only declares `exposed`, so:
#
#   - by default, `hidden` is emitted as `static uint32_t hidden(...)` and
#     does not appear in the header;
#   - with `--ext no_krml_private`, it is emitted as a normal, externally
#     visible `uint32_t KrmlPrivateTest_hidden(...)` and is declared in the
#     header.
#
# NB: the flag is consumed at typechecking time, so each variant needs its
# own cache directory.

# mk/test.mk defaults KRML_EXE to $(FSTAR_ROOT)/out/bin/krml, which only
# exists in a dev tree. `make install` also puts krml next to fstar.exe, so
# try that too. If krml is nowhere to be found we skip (loudly), unless
# REQUIRE_BACKENDS=1.
KRML_CANDIDATES := $(KRML_EXE) $(dir $(FSTAR_EXE))krml $(FSTAR_ROOT)/karamel/out/bin/krml
KRML_FOUND      := $(firstword $(wildcard $(KRML_CANDIDATES)) $(shell command -v krml 2>/dev/null))
ifneq ($(KRML_FOUND),)
  override KRML_EXE := $(KRML_FOUND)
endif

ifneq ($(KRML_FOUND),)
all: $(OUTPUT_DIR)/private.checked $(OUTPUT_DIR)/nonprivate.checked
else
ifeq ($(REQUIRE_BACKENDS),1)
  $(error krml not found (looked in $(KRML_CANDIDATES) and on PATH), and REQUIRE_BACKENDS=1)
endif
all:
	@echo "SKIP: krml not found, not testing --ext no_krml_private"
endif

# $(1) = variant name, $(2) = extra F* flags
define krml_variant
$(OUTPUT_DIR)/$(1)/KrmlPrivateTest.c: KrmlPrivateTest.fsti KrmlPrivateTest.fst $(FSTAR_EXE)
	$$(call msg, "EXTRACT", "KrmlPrivateTest ($(1))")
	$$(Q)rm -rf $(OUTPUT_DIR)/$(1) && mkdir -p $(OUTPUT_DIR)/$(1)
	$$(Q)$$(FSTAR_EXE) $$(SIL) $(2) --cache_checked_modules \
	  --odir $(OUTPUT_DIR)/$(1) --cache_dir $(OUTPUT_DIR)/$(1) KrmlPrivateTest.fsti
	$$(Q)$$(FSTAR_EXE) $$(SIL) $(2) --cache_checked_modules \
	  --odir $(OUTPUT_DIR)/$(1) --cache_dir $(OUTPUT_DIR)/$(1) KrmlPrivateTest.fst
	$$(Q)$$(FSTAR_EXE) $$(SIL) $(2) --codegen krml --extract_module KrmlPrivateTest \
	  --odir $(OUTPUT_DIR)/$(1) --cache_dir $(OUTPUT_DIR)/$(1) \
	  $(OUTPUT_DIR)/$(1)/KrmlPrivateTest.fst.checked
	$$(call msg, "KRML", "KrmlPrivateTest ($(1))")
	$$(Q)$$(KRML_EXE) -skip-makefiles -skip-compilation \
	  -header=$$(FSTAR_ROOT)/mk/krmlheader \
	  $(OUTPUT_DIR)/$(1)/KrmlPrivateTest.krml -tmpdir $(OUTPUT_DIR)/$(1) >/dev/null
endef

$(eval $(call krml_variant,private,))
$(eval $(call krml_variant,nonprivate,--ext no_krml_private))

$(OUTPUT_DIR)/private.checked: $(OUTPUT_DIR)/private/KrmlPrivateTest.c
	$(call msg, "CHECK", "hidden is static")
	$(Q)grep -q '^static uint32_t hidden(' $<
	$(Q)! grep -q 'KrmlPrivateTest_hidden' $(OUTPUT_DIR)/private/KrmlPrivateTest.h
	$(Q)touch $@

$(OUTPUT_DIR)/nonprivate.checked: $(OUTPUT_DIR)/nonprivate/KrmlPrivateTest.c
	$(call msg, "CHECK", "hidden is public")
	$(Q)! grep -q '^static uint32_t hidden(' $<
	$(Q)grep -q '^uint32_t KrmlPrivateTest_hidden(' $<
	$(Q)grep -q 'KrmlPrivateTest_hidden' $(OUTPUT_DIR)/nonprivate/KrmlPrivateTest.h
	$(Q)touch $@
