PULSE_HOME ?= ../..
PULSE_EXAMPLES_ROOT ?= $(PULSE_HOME)/share/pulse/examples

SRC_DIRS := $(addprefix $(PULSE_EXAMPLES_ROOT)/,by-example dice/external dice/external/hacl dice/external/l0 dice/dpe dice/engine dice/l0)
ifneq (,$(wildcard $(PULSE_EXAMPLES_ROOT)/dice/_output/cache))
SRC_DIRS += $(PULSE_EXAMPLES_ROOT)/dice/_output/cache
endif
# ifneq (,$(wildcard $(PULSE_EXAMPLES_ROOT)/dice/common/hacl-c/_output/cache))
# SRC_DIRS += $(PULSE_EXAMPLES_ROOT)/dice/common/hacl-c/_output/cache
# endif
ifneq (,$(wildcard $(PULSE_EXAMPLES_ROOT)/_output/cache))
SRC_DIRS += $(PULSE_EXAMPLES_ROOT)/_output/cache
endif
OUTPUT_DIRECTORY := _output
CACHE_DIRECTORY := $(OUTPUT_DIRECTORY)/cache
FSTAR_OPTIONS += --warn_error -342 --cmi

MAIN=../main.exe
RUST_SRC_DIR=./src/
DPE_OUTPUT_DIR=../dpe/src/generated

all: test dpe

include $(PULSE_HOME)/share/pulse/Makefile.include

FSTAR_DEP_OPTIONS=--extract '* -FStar.Tactics -FStar.Reflection -Pulse +Pulse.Class +Pulse.Lib -Pulse.Lib.Core'

# The following note is from share/pulse/examples/dice/Makefile
# where a copy of the %.ast rule existed

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
		$(FSTAR) --admit_smt_queries true --codegen Extension $(subst .ast,.fst, $(subst _,., $(notdir $@))) --extract_module $(basename $(subst .ast,.fst, $(subst _,., $(notdir $@))))

pulsetutorial-array.rs: PulseTutorial_Array.ast
	$(MAIN) -odir $(RUST_SRC_DIR) $(addprefix $(OUTPUT_DIRECTORY)/, $^)

pulsetutorial-loops.rs: PulseTutorial_Loops.ast
	$(MAIN) -odir $(RUST_SRC_DIR) $(addprefix $(OUTPUT_DIRECTORY)/, $^)

pulsetutorial-algorithms.rs: PulseTutorial_Algorithms.ast
	$(MAIN) -odir $(RUST_SRC_DIR) $(addprefix $(OUTPUT_DIRECTORY)/, $^)

DPE_FILES = EngineTypes.ast \
  EngineCore.ast \
	HACL.ast \
	L0Types.ast \
	Pulse_Lib_HashTable_Type.ast \
	Pulse_Lib_HashTable_Spec.ast \
	Pulse_Lib_HashTable.ast \
	DPETypes.ast \
	DPE.ast

DPE_LIB = L0Core,Pulse.Lib.Array,FStar.SizeT,EverCrypt.HMAC,EverCrypt.Hash.Incremental,EverCrypt.Ed25519,EverCrypt.AutoConfig2,Spec.Hash.Definitions

dpe.rs: $(DPE_FILES)
	$(MAIN) -odir $(DPE_OUTPUT_DIR)/ -lib $(DPE_LIB) $(addprefix $(OUTPUT_DIRECTORY)/, $^)

all-rs: pulsetutorial-loops.rs pulsetutorial-algorithms.rs

test: all-rs
	cargo test

.PHONY: external
external:
	../dpe/gen-rust-bindings.sh

dpe: dpe.rs external
	cd ../dpe && cargo build && cd -
	$(MAKE) -C ../dpe -f c.Makefile

.PHONY: test dpe
