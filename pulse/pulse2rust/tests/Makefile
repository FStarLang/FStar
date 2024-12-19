PULSE_ROOT ?= ../..
OUTPUT_DIR=_output
CACHE_DIR=_cache
CODEGEN=Extension
TAG=pulse2rust

NO_OCAML := 1

PULSE_EXAMPLES_ROOT ?= $(PULSE_ROOT)/share/pulse/examples
SRC:=$(PULSE_EXAMPLES_ROOT) # Actually does not matter much

SRC_DIRS := $(addprefix $(PULSE_EXAMPLES_ROOT)/,. by-example dice/cbor dice/external dice/external/hacl dice/external/l0 dice/dpe dice/engine dice/l0)

# I don't like this
OTHERFLAGS += $(addprefix --include ,$(SRC_DIRS))

ROOTS = -d # hehe

OTHERFLAGS += --include $(PULSE_EXAMPLES_ROOT)/_cache
OTHERFLAGS += --include $(PULSE_EXAMPLES_ROOT)/by-example/_cache
OTHERFLAGS += --include $(PULSE_EXAMPLES_ROOT)/dice/_cache
OTHERFLAGS += --include $(PULSE_EXAMPLES_ROOT)/dice/common/hacl-c/_cache

OTHERFLAGS += --warn_error -342 --cmi
OTHERFLAGS += --include $(PULSE_ROOT)/out/lib/pulse

include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := all

MAIN=../main.exe
RUST_SRC_DIR=src
RUST_OUT_DIR=out
DPE_OUTPUT_DIR=../dpe/src/generated

.PHONY: all
all: test dpe


FSTAR_DEP_OPTIONS=--extract '* -FStar.Tactics -FStar.Reflection -Pulse +Pulse.Class +Pulse.Lib -Pulse.Lib.Core'

# The following note is from share/pulse/examples/dice/Makefile
# where a copy of the %.ast rule existed

# FIXME: this rule should depend on the .checked file. However, right
# now there is no way to reconcile the cache directories. There are
# currently two modes:
#
# * share/pulse/examples/dice/Makefile produces the DICE .checked
#   files in a single directory, _cache, but it assumes (with
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

$(OUTPUT_DIR)/%.ast:
		$(FSTAR) --admit_smt_queries true --codegen Extension $(subst .ast,.fst, $(subst _,., $(notdir $@))) --extract_module $(basename $(subst .ast,.fst, $(subst _,., $(notdir $@))))

$(RUST_SRC_DIR)/pulsetutorial_array.rs: $(OUTPUT_DIR)/PulseTutorial_Array.ast
	$(MAIN) -odir $(RUST_SRC_DIR) $+

$(RUST_SRC_DIR)/pulsetutorial_loops.rs: $(OUTPUT_DIR)/PulseTutorial_Loops.ast
	$(MAIN) -odir $(RUST_SRC_DIR) $+

$(RUST_SRC_DIR)/pulsetutorial_algorithms.rs: $(OUTPUT_DIR)/PulseTutorial_Algorithms.ast
	$(MAIN) -odir $(RUST_SRC_DIR) $+

$(RUST_SRC_DIR)/example_slice.rs: $(OUTPUT_DIR)/Example_Slice.ast
	$(MAIN) -odir $(RUST_SRC_DIR) $+

%.rlib: %.rs
	rustc --crate-type rlib -o $@ $+

DPE_FILES = $(addprefix $(OUTPUT_DIR)/, \
	EngineTypes.ast \
	EngineCore.ast \
	HACL.ast \
	L0Types.ast \
	Pulse_Lib_HashTable_Type.ast \
	Pulse_Lib_HashTable_Spec.ast \
	Pulse_Lib_HashTable.ast \
	DPETypes.ast \
	DPE.ast \
)

DPE_LIB = L0Core,Pulse.Lib.Array,FStar.SizeT,EverCrypt.HMAC,EverCrypt.Hash.Incremental,EverCrypt.Ed25519,EverCrypt.AutoConfig2,Spec.Hash.Definitions

.PHONY: dpe.rs
dpe.rs: $(DPE_FILES)
	$(MAIN) -odir $(DPE_OUTPUT_DIR)/ -lib $(DPE_LIB) $^

.PHONY: all-rs
all-rs: $(addprefix $(RUST_SRC_DIR)/, pulsetutorial_loops.rlib pulsetutorial_algorithms.rs pulsetutorial_array.rs example_slice.rlib)

.PHONY: test
test: all-rs
	cargo test

.PHONY: external
external:
	../dpe/gen-rust-bindings.sh

.PHONY: dpe
dpe: dpe.rs external
	cd ../dpe && cargo build && cd -
	$(MAKE) -C ../dpe -f c.Makefile

.PHONY: test dpe
