include ../Makefile.common

FSTAR:=${FSTAR_HOME}/bin/fstar.exe $(SMT) --ide --warn_error -282 --ext fstar:no_absolute_paths

# Feed .in to F* and record output as .out.  Output is passed through cleanup.py
# to ensure that the output is deterministic by pretty-printing JSON messages
# (otherwise the order of fields in JSON dictionaries might vary across runs)
# We turn off the .checked file cache so we don't get any races in CI
# because we run multiple F* processes for the same *.fst file in parallel.
%.out: %.in $(FSTAR_HOME)/bin/fstar.exe
	$(call msg, "OUT_IDE", $<)
	$(Q)$(eval FST := $(firstword $(subst ., ,$<)))
	$(Q)$(FSTAR) --cache_off "$(realpath ${FST}.fst)" < "$<" | $(JSON_CLEANUP) "$@"

# The Harness.* tests for the push-partial-checked-file request require Harness.fst.checked
Harness.%.out: Harness.%.in $(FSTAR_HOME)/bin/fstar.exe Harness.fst.checked
	$(call msg, "OUT_IDE", $<)
	$(Q)$(eval FST := $(firstword $(subst ., ,$<)))
	$(Q)$(FSTAR) "$(realpath ${FST}.fst)" < "$<" | $(JSON_CLEANUP) "$@"

%.checked: %
	$(call msg, "CHECK", $<)
	$(Q)$(FSTAR_HOME)/bin/fstar.exe $(SMT) --cache_checked_modules --silent $<

.depend:
	$(call msg, "DEPEND")
	$(Q)$(FSTAR) --dep full $(wildcard *.fst *.fsti) > .depend
include .depend