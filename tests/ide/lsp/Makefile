include ../Makefile.common

FSTAR:=${FSTAR_HOME}/bin/fstar.exe $(SMT) --lsp --warn_error -282

# Feed .in to F* and record output as .out.  Output is passed through cleanup.py
# to ensure that the output is deterministic by pretty-printing JSON messages
# (otherwise the order of fields in JSON dictionaries might vary across runs)
# We turn off the .checked file cache so we don't get any races in CI
%.out: %.in $(FSTAR_HOME)/bin/fstar.exe
	$(call msg, "OUT_LSP", $<)
	$(Q)$(FSTAR) < "$<" 2>&1 | $(JSON_CLEANUP) "$@"

