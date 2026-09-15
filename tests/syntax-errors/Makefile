FSTAR_ROOT ?= ../..

# The files in this directory fail to parse or to desugar, so we cannot run a
# dependency analysis on them, nor verify them. We only check the error F*
# reports.
NODEPEND=1
NOVERIFY=1

include $(FSTAR_ROOT)/mk/test.mk

# This so that we don't get warnings about:
# 241: "unable to load checked file"
# 247: "checked file was not written"
# 333: "unable to read hints"
OTHERFLAGS+=--warn_error -241-247-333

OTHERFLAGS := $(filter-out --query_stats, $(OTHERFLAGS))
OTHERFLAGS := $(filter-out --hint_info, $(OTHERFLAGS))
OTHERFLAGS += --ext fstar:no_absolute_paths

# Unlike tests/error-messages, F* exits with a non-zero status on these files,
# so we use our own rule (note the leading '-') rather than the %.output one.
$(OUTPUT_DIR)/%.fst.errout: %.fst
	$(call msg, "OUTPUT", $(basename $(notdir $@)))
	@mkdir -p $(dir $@)
	-$(FSTAR) --message_format human --silent -f $< >$@ 2>&1
