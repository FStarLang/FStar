FSTAR_ROOT ?= ../../..
include $(FSTAR_ROOT)/mk/test.mk

# 'strict' turns a surviving ambiguity into an error instead of resolving
# it by scope order. It is not meant for checking real code; it exists to
# find where genuine ambiguity arises.
FSTAR_ARGS += --ext fstar:overload=strict

# The .output rule does not go through the dependency graph, so make the
# dependencies explicit: otherwise the expected output picks up a
# "checked file does not exist" warning depending on scheduling.
$(OUTPUT_DIR)/StrictAmbiguous.fst.output: $(CACHE_DIR)/StrictInt.fst.checked $(CACHE_DIR)/StrictBool.fst.checked
$(OUTPUT_DIR)/StrictDuplicate.fst.output: $(CACHE_DIR)/StrictInt.fst.checked $(CACHE_DIR)/StrictBool.fst.checked
