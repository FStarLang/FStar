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

# FIXME: this rule should depend on the .checked file. However, right
# now there is no way to reconcile the cache directories. There are
# currently two modes:
#
# * share/pulse/examples/dice/Makefile produces the DICE .checked
#   files in a single directory, _output/cache, but it assumes (with
#   --already_cached) that the .checked files from the Pulse standard
#   library already exist somewhere else.
#
# * src/verify.Makefile currently produces each .checked file next to
#   its corresponding source file, thus with no cache directory
# 
# Alternatively, the latter verify.Makefile could produce everything
# in one single cache directory, but in that case, all examples would
# need to use that cache directory. This will work for CI but is not
# desirable for end-users since:
#
# 1/ it will unnecessarily increase build time with example files
# whose interface is not guaranteed to be stable (and thus users
# should not write modules that depend on such examples), and
# 
# 2/ that cache directory will contain .checked files for example
# modules without a namespace, which will likely clash with end-users'
# modules once `--include`d.
#
# So, I believe the solution here is to make `fstar.exe --dep full`
# produce dependency rules for .ast files, which will automatically
# compute the right location for each .checked file, and a list of
# ALL_AST_FILES, as is already done with .ml and .krml extracted
# files. If so, then this %.ast rule will be generic and can move to
# share/pulse/Makefile.include-base.
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
