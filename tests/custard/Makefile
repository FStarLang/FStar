FSTAR_ROOT ?= ../..

# Each of these modules is extracted with --codegen Custard, starting from its
# 'main' entry point, then compiled and run; the output is compared against
# the corresponding .out.expected file.
CUSTARD_TESTS += Hello
CUSTARD_TESTS += Recursion
CUSTARD_TESTS += Datatypes
CUSTARD_TESTS += Typeclass
CUSTARD_TESTS += Unroll
CUSTARD_TESTS += Layouts
CUSTARD_TESTS += Effects
CUSTARD_TESTS += Curried
CUSTARD_TESTS += Implicits

# Extraction of each of these must fail with the given error code: they are
# the diagnostics of sections 3.2 and 3.6.
REJECT_TESTS += MonoPoly
REJECT_TESTS += MonoPartial
REJECT_TESTS += MonoFuel
CODE_MonoPoly    = 363
CODE_MonoPartial = 363
CODE_MonoFuel    = 364

include $(FSTAR_ROOT)/mk/test.mk

# Override the default OCaml extraction rule from test.mk: we drive the Custard
# pipeline instead, which is whole-program and hence keyed on an entry point.
$(OUTPUT_DIR)/%.ml:
	$(call msg, "CUSTARD", $(basename $(notdir $@)))
	$(FSTAR) --codegen Custard --custard_entry $*.main $< -o $@

$(OUTPUT_DIR)/%.rejected: $(CACHE_DIR)/%.fst.checked
	$(call msg, "REJECT", $(basename $(notdir $@)))
	@mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) --message_format human --codegen Custard --custard_entry $*.main \
	  $< >$(OUTPUT_DIR)/$*.err 2>&1 || true
	$(Q)grep -q "Error $(CODE_$*)" $(OUTPUT_DIR)/$*.err \
	  || { echo "ERROR: expected error $(CODE_$*) from $*"; cat $(OUTPUT_DIR)/$*.err; false; }
	$(Q)touch $@

all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .out.diff, $(CUSTARD_TESTS)))
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .rejected, $(REJECT_TESTS)))
