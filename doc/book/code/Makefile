FSTAR_ROOT ?= ../../..
include $(FSTAR_ROOT)/mk/test.mk

FSTAR_FILES := $(filter-out ContextPollution.fst MemCpy.Deps.fst MemCpy.fst,$(FSTAR_FILES))

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
