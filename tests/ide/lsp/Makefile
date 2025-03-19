OTHERFLAGS += --lsp --warn_error -282 --ext fstar:no_absolute_paths
NOVERIFY=1
FSTAR_ROOT ?= ../../..
include $(FSTAR_ROOT)/mk/test.mk

_ != mkdir -p $(OUTPUT_DIR)

JSON_CLEANUP=python ../cleanup.py

# Feed .in to F* and record output as .ideout.  Output is passed through cleanup.py
# to ensure that the output is deterministic by pretty-printing JSON messages
# (otherwise the order of fields in JSON dictionaries might vary across runs)
$(OUTPUT_DIR)/%.ideout: %.in
	$(call msg, "OUT_LSP", $<)
	$(FSTAR) < "$<" 2>&1 | $(JSON_CLEANUP) "$@"
