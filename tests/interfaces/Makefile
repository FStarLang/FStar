# The implementations here are meant to be rejected: an interface
# declaration that is left unimplemented, implemented out of order, or
# implemented by a definition that does not subsume it. These are
# module-level errors, so they cannot be wrapped in [@@expect_failure]
# and F* exits with a non-zero status. Only the recorded output is
# compared; the files are not expected to check.
NOVERIFY := 1

FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

OTHERFLAGS += --ext fstar:no_absolute_paths

# Remove --query_stats and --hint_info from this subdir, since
# they output timing info.
OTHERFLAGS := $(filter-out --query_stats, $(OTHERFLAGS))
OTHERFLAGS := $(filter-out --hint_info, $(OTHERFLAGS))

FAILING := $(patsubst %.fst,%,$(wildcard Iface*.fst))

$(patsubst %,$(OUTPUT_DIR)/%.fst.output,$(FAILING)): $(OUTPUT_DIR)/%.fst.output: %.fst
	$(call msg, "OUTPUT", $(basename $(notdir $@)))
	@mkdir -p $(dir $@)
	-$(FSTAR) --message_format human --silent -f $< >$@ 2>&1

$(patsubst %,$(OUTPUT_DIR)/%.fst.json_output,$(FAILING)): $(OUTPUT_DIR)/%.fst.json_output: %.fst
	$(call msg, "JSONOUT", $(basename $(notdir $@)))
	@mkdir -p $(dir $@)
	-$(FSTAR) --message_format json --silent -f $< >$@ 2>&1
