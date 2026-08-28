FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

SUBDIRS += ns_resolution

# These definitions agree with the erasability their interface declares, so
# none of them may raise 318. The cases that do are in tests/interfaces.
$(CACHE_DIR)/MustEraseForExtraction.fst.checked: FSTAR_ARGS += --warn_error @318
FSTAR_ARGS += --warn_error +240

# `--ext freshen` restarts the solver before every top-level declaration.
# ExtFreshen.fst is written so that each declaration depends on facts
# introduced by the previous ones, so checking it with the option on tests
# that the SMT context is properly replayed across the restarts.
$(CACHE_DIR)/ExtFreshen.fst.checked: FSTAR_ARGS += --ext freshen

# And check that the restarts really do happen: --query_stats reports every
# Z3 process it spawns, and there must be several of them when the option is
# on but only one when it is off.
all: $(OUTPUT_DIR)/ExtFreshen.restarts

$(OUTPUT_DIR)/ExtFreshen.restarts: ExtFreshen.fst $(FSTAR_EXE)
	$(call msg, "FRESHEN", $<)
	$(Q)rm -rf $(OUTPUT_DIR)/freshen-on $(OUTPUT_DIR)/freshen-off
	$(Q)mkdir -p $(OUTPUT_DIR)/freshen-on $(OUTPUT_DIR)/freshen-off
	$(Q)$(FSTAR_EXE) $(SIL) --query_stats --ext freshen \
	  --odir $(OUTPUT_DIR)/freshen-on --cache_dir $(OUTPUT_DIR)/freshen-on $< \
	  > $(OUTPUT_DIR)/freshen-on.out 2>&1
	$(Q)$(FSTAR_EXE) $(SIL) --query_stats \
	  --odir $(OUTPUT_DIR)/freshen-off --cache_dir $(OUTPUT_DIR)/freshen-off $< \
	  > $(OUTPUT_DIR)/freshen-off.out 2>&1
	$(Q)on=$$(grep -c 'Creating new z3proc' $(OUTPUT_DIR)/freshen-on.out); \
	  off=$$(grep -c 'Creating new z3proc' $(OUTPUT_DIR)/freshen-off.out); \
	  if [ "$$off" -ne 1 ]; then \
	    echo "ERROR: expected 1 Z3 process without --ext freshen, got $$off"; false; \
	  fi; \
	  if [ "$$on" -le "$$off" ]; then \
	    echo "ERROR: --ext freshen did not restart Z3 ($$on processes, vs $$off without)"; false; \
	  fi
	$(Q)touch $@
