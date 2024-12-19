# PULSE_HOME ?= ../../../..
# PULSE_EXAMPLES_ROOT = $(PULSE_HOME)/share/pulse/examples
# OUTPUT_DIRECTORY=_output
# CACHE_DIRECTORY=$(OUTPUT_DIRECTORY)/cache
# SRC_DIRS = dpe engine l0 external external/hacl external/l0
# INCLUDE_PATHS += cbor
# #/Pulse.Lib.HashTable.fst
# FSTAR_OPTIONS += --warn_error -342
# FSTAR_DEP_OPTIONS=--extract '* -FStar.Tactics -FStar.Reflection -Pulse +Pulse.Class +Pulse.Lib -Pulse.Lib.Core'
# all: verify

# include $(PULSE_HOME)/share/pulse/Makefile.include

# .PHONY: test-c
# test-c: verify
#         +$(MAKE) -f c.Makefile


# NOTE!!!!: no subdirs, we just rely on fstar.include
# Otherwise we need to state cross-dependencies in each of them,
# SUBDIRS += cbor
# SUBDIRS += dpe
# SUBDIRS += engine
# SUBDIRS += l0
# SUBDIRS += external

# Start dep analysis from every file under here.
FSTAR_FILES != find . -name '*.fst' -o -name '*.fsti'

PULSE_ROOT ?= ../../../..
include $(PULSE_ROOT)/mk/test.mk
