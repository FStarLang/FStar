include ../Makefile.common

OTHERFLAGS += --lsp --warn_error -282

# Feed .in to F* and record output as .out.  Output is passed through cleanup.py
# to ensure that the output is deterministic by pretty-printing JSON messages
# (otherwise the order of fields in JSON dictionaries might vary across runs)
%.out: %.in
	$(call msg, "OUT_LSP", $<)
	$(Q)$(FSTAR) < "$<" 2>&1 | $(JSON_CLEANUP) "$@"
