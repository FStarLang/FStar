OTHERFLAGS += --warn_error -282 --ext fstar:no_absolute_paths
NOVERIFY=1
FSTAR_ROOT ?= ../../..
include $(FSTAR_ROOT)/mk/test.mk

_ != mkdir -p $(OUTPUT_DIR)

JSON_CLEANUP=python ../cleanup.py

# Feed .in to F* and record output as .ideout.  Output is passed through cleanup.py
# to ensure that the output is deterministic by pretty-printing JSON messages
# (otherwise the order of fields in JSON dictionaries might vary across runs)
$(OUTPUT_DIR)/%.ideout: %.in
	$(call msg, "OUT_IDE", $<)
	$(eval FST := $(firstword $(subst ., ,$<)))
	$(FSTAR) --ide --silent "$(realpath ${FST}.fst)" < "$<" | $(JSON_CLEANUP) "$@"

# The Missing* tests require a predictable full path
$(OUTPUT_DIR)/Missin%.ideout: Missin%.in
	$(call msg, "OUT_IDE", $<)
	$(FSTAR) --ide --silent /Missing.fst < "$<" | $(JSON_CLEANUP) "$@"

# The Harness.* tests for the push-partial-checked-file request require Harness.fst.checked
$(OUTPUT_DIR)/Harness.%.ideout: Harness.%.in $(CACHE_DIR)/Harness.fst.checked
	$(call msg, "OUT_IDE", $<)
	$(Q)$(eval FST := $(firstword $(subst ., ,$<)))
	$(Q)$(FSTAR) --ide "$(realpath ${FST}.fst)" < "$<" | $(JSON_CLEANUP) "$@"
