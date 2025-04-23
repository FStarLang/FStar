FSTAR_ROOT ?= ../..
FSTAR_FILES = $(wildcard Test*.fst)
OTHERFLAGS += --warn_error -272 # top-level effects
include $(FSTAR_ROOT)/mk/test.mk

all: BigList.memcheck

# Test that this file does not use much memory (currently ~500MB),
# we give it 1.5GB
BigList.memcheck: BigList.fst
	$(call msg, "MEMCHECK", $<)
	( ulimit -d 1500000 && $(FSTAR) BigList.fst )
	touch $@
