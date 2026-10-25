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

# The OvlIde.* tests look a name up in a module that opens two others which
# both define it. The fixtures must already be checked when the session
# starts, or the output would depend on whether $(CACHE_DIR) happens to be
# populated: an unchecked dependency adds a warning to the first response.
$(OUTPUT_DIR)/OvlIde.%.ideout: OvlIde.%.in $(CACHE_DIR)/OvlIdeInt.fst.checked $(CACHE_DIR)/OvlIdeBool.fst.checked
	$(call msg, "OUT_IDE", $<)
	$(FSTAR) --ide --silent "$(realpath OvlIde.fst)" < "$<" | $(JSON_CLEANUP) "$@"

HIERARCHICAL_DIR := $(abspath hierarchical)

$(CACHE_DIR)/A.B.C.fst.checked: $(HIERARCHICAL_DIR)/A/B/C.fst
	$(call msg, "CHECK", $(notdir $<))
	$(FSTAR) --include "$(HIERARCHICAL_DIR)" -c $< -o $@

# Check resolved and include-relative ranges against the same snapshot. Keep
# directory components so a basename-only response fails in either mode.
$(OUTPUT_DIR)/Hierarchical.%.ideout: Hierarchical.%.in $(CACHE_DIR)/A.B.C.fst.checked
	$(call msg, "OUT_IDE", $<)
	$(FSTAR) --ext fstar:no_absolute_paths=false --include "$(HIERARCHICAL_DIR)" \
	  --ide --silent "$(HIERARCHICAL_DIR)/Client/Lookup.fst" < "$<" \
	  | $(JSON_CLEANUP) "$@" "$(HIERARCHICAL_DIR)"
	$(FSTAR) --ext fstar:no_absolute_paths --include "$(HIERARCHICAL_DIR)" \
	  --ide --silent "$(HIERARCHICAL_DIR)/Client/Lookup.fst" < "$<" \
	  | $(JSON_CLEANUP) "$@.relative" "$(HIERARCHICAL_DIR)"
	cmp "$@" "$@.relative"
