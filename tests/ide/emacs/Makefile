include ../Makefile.common

.DELETE_ON_ERROR:

OTHERFLAGS += --warn_error -282 --ext fstar:no_absolute_paths

# Feed .in to F* and record output as .out.  Output is passed through cleanup.py
# to ensure that the output is deterministic by pretty-printing JSON messages
# (otherwise the order of fields in JSON dictionaries might vary across runs)
%.out: %.in
	$(call msg, "OUT_IDE", $<)
	$(Q)$(eval FST := $(firstword $(subst ., ,$<)))
	$(Q)$(FSTAR) --ide --silent "$(realpath ${FST}.fst)" < "$<" | $(JSON_CLEANUP) "$@"

# The Harness.* tests for the push-partial-checked-file request require Harness.fst.checked
Harness.%.out: Harness.%.in $(CACHE_DIR)/Harness.fst.checked
	$(call msg, "OUT_IDE", $<)
	$(Q)$(eval FST := $(firstword $(subst ., ,$<)))
	$(Q)$(FSTAR) --ide "$(realpath ${FST}.fst)" < "$<" | $(JSON_CLEANUP) "$@"

# Only here for Harness.fst.checked
%.checked: %
	$(call msg, "CHECK", $<)
	$(Q)$(FSTAR) --cache_checked_modules --silent $<

.depend:
	$(call msg, "DEPEND")
	$(Q)$(FSTAR) --dep full $(wildcard *.fst *.fsti) --output_deps_to .depend
include .depend
