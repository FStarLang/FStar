PULSE_HOME ?= ../../../..
PULSE_EXAMPLES_ROOT = $(PULSE_HOME)/share/pulse/examples
OUTPUT_DIRECTORY=_output
CACHE_DIRECTORY=$(OUTPUT_DIRECTORY)/cache
SRC_DIRS = dpe engine l0 external external/hacl external/l0
INCLUDE_PATHS += cbor
#/Pulse.Lib.HashTable.fst
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_OPTIONS=--extract '* -FStar.Tactics -FStar.Reflection -Pulse +Pulse.Class +Pulse.Lib -Pulse.Lib.Core'

.PHONY: all test-c
all: verify

include $(PULSE_HOME)/share/pulse/Makefile.include

.PHONY: test-c
test-c: verify
	+$(MAKE) -f c.Makefile
