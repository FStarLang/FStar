FSTAR_ROOT ?= ../../..
include $(FSTAR_ROOT)/mk/test.mk

# 'strict' turns a surviving ambiguity into an error instead of silently
# keeping the answer name resolution gives today. It is not meant to be
# used to check real code; it exists to find out where genuine ambiguity
# arises, which is how we decide whether 'compat' can become the default.
FSTAR_ARGS += --ext fstar:overload=strict

# The .output rule does not go through the dependency graph, so make the
# dependencies explicit: otherwise the expected output picks up a
# "checked file does not exist" warning depending on scheduling.
$(OUTPUT_DIR)/StrictAmbiguous.fst.output: $(CACHE_DIR)/StrictInt.fst.checked $(CACHE_DIR)/StrictBool.fst.checked
