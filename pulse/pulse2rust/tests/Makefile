PULSE_HOME ?= ../..
PULSE_EXAMPLES_ROOT ?= $(PULSE_HOME)/share/pulse/examples

SRC_DIRS := $(addprefix $(PULSE_EXAMPLES_ROOT)/,by-example dice/common dice/dpe dice/engine dice/l0)
OUTPUT_DIRECTORY := _output
CACHE_DIRECTORY := $(OUTPUT_DIRECTORY)/cache

MAIN=../main.exe
RUST_SRC_DIR=./src/

all: test

include $(PULSE_HOME)/share/pulse/Makefile.include

FSTAR_DEP_OPTIONS=--extract '* -FStar.Tactics -FStar.Reflection -Pulse +Pulse.Class +Pulse.Lib -Pulse.Lib.Core'

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
	L0Types.ast \
	L0Crypto.ast \
	L0Core.ast \
	Pulse_Lib_HashTable_Type.ast \
	Pulse_Lib_HashTable_Spec.ast \
	Pulse_Lib_HashTable.ast \
	DPETypes.ast \
	DPE.ast

dpe.rs: $(DPE_FILES)
	$(MAIN) -odir $(RUST_SRC_DIR)/dpe_ $(addprefix $(OUTPUT_DIRECTORY)/, $^)

all-rs: pulsetutorial-loops.rs pulsetutorial-algorithms.rs dpe.rs  #pulsetutorial-array.rs

test: all-rs
	cargo test

.PHONY: test
