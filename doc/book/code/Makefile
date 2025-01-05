FSTAR_ROOT ?= ../../..
include $(FSTAR_ROOT)/mk/test.mk

FSTAR_FILES := $(filter-out ContextPollution.fst,$(FSTAR_FILES))

# Disable context pruning for this file, fails otherwise.
$(CACHE_DIR)/Alex.fst.checked: OTHERFLAGS += --ext context_pruning=

exercises:
	$(MAKE) -C exercises

all: exercises

wc:
	# Prims.fst seems to be missing here?
	wc -l Prims.fst $(ALL)

extract:
	krml -skip-compilation MemCpy.fst -tmpdir out

clean:
	$(MAKE) -C exercises clean
