PULSE_ROOT ?= ../..
include $(PULSE_ROOT)/mk/test.mk

# Ensure output directories exist
$(shell mkdir -p _output _cache)

# Suppress warnings that add noise to expected output
OTHERFLAGS+=--warn_error -241-247-333-274-152-285

# Remove --query_stats and --hint_info since they output timing info
OTHERFLAGS := $(filter-out --query_stats, $(OTHERFLAGS))
OTHERFLAGS := $(filter-out --hint_info, $(OTHERFLAGS))

# Strip absolute paths for reproducibility
OTHERFLAGS += --ext fstar:no_absolute_paths
