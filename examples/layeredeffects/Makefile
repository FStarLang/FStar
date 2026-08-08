OTHERFLAGS+=--already_cached 'Prims FStar LowStar'

FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

all: extraction

.PHONY: extraction
extraction:
	$(MAKE) -C extraction FSTAR_EXE=$(FSTAR_EXE)
