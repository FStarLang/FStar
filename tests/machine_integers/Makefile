FSTAR_ROOT ?= ../..
FSTAR_FILES = $(wildcard Test*.fst)
OTHERFLAGS += --warn_error -272 # top-level effects
include $(FSTAR_ROOT)/mk/test.mk

all: BigList.memcheck BigListNorm.timecheck

# Test that this file does not use much memory (currently ~500MB),
# we give it 1.5GB
BigList.memcheck: BigList.fst
	$(call msg, "MEMCHECK", $<)
	( ulimit -d 1500000 && $(FSTAR) BigList.fst )
	touch $@

# Regression test for issue #4394: normalizing a recursive function over a
# large list must not take quadratic time. This currently takes a few seconds;
# before the fix it took about a minute.
BigListNorm.timecheck: BigListNorm.fst
	$(call msg, "TIMECHECK", $<)
	timeout 40 $(FSTAR) BigListNorm.fst
	touch $@
