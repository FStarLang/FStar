PULSE_HOME ?= ../../../..
PULSE_EXAMPLES_ROOT = $(PULSE_HOME)/share/pulse/examples
OUTPUT_DIRECTORY=_output
CACHE_DIRECTORY=$(OUTPUT_DIRECTORY)/cache
SRC_DIRS = common dpe engine l0
INCLUDE_PATHS += cbor
#/Pulse.Lib.HashTable.fst
FSTAR_DEP_OPTIONS=--extract '* -FStar.Tactics -FStar.Reflection -Pulse +Pulse.Class +Pulse.Lib -Pulse.Lib.Core'
all: verify dpe-ast

include $(PULSE_HOME)/share/pulse/Makefile.include

# FIXME: this rule should depend on the .checked files. However, right
# now there is no way to reconcile the cache directories: this
# Makefile generates the .checked files in _output/cache, but
# src/verify.Makefile, which verifies everything in parallel for CI,
# generates each .checked file next to its source file. Alternatively,
# the latter verify.Makefile could produce everything in one single
# cache directory, but in that case, all examples would need to use
# that cache directory.

%.ast:
	$(FSTAR) --admit_smt_queries true --warn_error -241 --codegen Extension $(subst .ast,, $(notdir $@)) --extract_module $(basename $(subst .ast,, $(notdir $@)))

DPE_FILES = EngineTypes.fst \
  EngineCore.fst \
	L0Types.fst \
	L0Crypto.fst \
	L0Core.fst \
	Pulse.Lib.HashTable.Type.fst \
	Pulse.Lib.HashTable.Spec.fst \
	Pulse.Lib.HashTable.fst \
	DPETypes.fst \
	DPE.fst

dpe-ast: $(addsuffix .ast, $(DPE_FILES))

.PHONY: dpe-ast
