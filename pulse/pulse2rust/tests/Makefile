STEEL_HOME=../..

INCLUDE_DIRS=lib by-example _output
OUTPUT_DIRECTORY=_output
CACHE_DIRECTORY=$(OUTPUT_DIRECTORY)/cache

SRC_DIRS=$(addprefix $(STEEL_HOME)/share/steel/examples/pulse/, $(INCLUDE_DIRS))
FSTAR_FILES=$(wildcard $(addsuffix /*.fst, $(SRC_DIRS))) $(wildcard $(addsuffix /*.fsti, $(SRC_DIRS)))

MAIN=../main.exe
RUST_SRC_DIR=./src/

all: test

include $(STEEL_HOME)/share/steel/examples/pulse/Makefile.pulse.common

FSTAR_DEP_OPTIONS=--extract '* -FStar.Tactics -FStar.Reflection -Steel -Pulse +Pulse.Class +Pulse.Lib -Pulse.Lib.Core'

%.ast:
		$(FSTAR) --admit_smt_queries true --codegen Extension $(subst .ast,.fst, $(subst _,., $(notdir $@))) --extract_module $(basename $(subst .ast,.fst, $(subst _,., $(notdir $@))))

pulsetutorial-array.rs: PulseTutorial_Array.ast
	$(MAIN) -odir $(RUST_SRC_DIR) $(addprefix $(OUTPUT_DIRECTORY)/, $^)

pulsetutorial-loops.rs: PulseTutorial_Loops.ast
	$(MAIN) -odir $(RUST_SRC_DIR) $(addprefix $(OUTPUT_DIRECTORY)/, $^)

pulsetutorial-algorithms.rs: PulseTutorial_Algorithms.ast
	$(MAIN) -odir $(RUST_SRC_DIR) $(addprefix $(OUTPUT_DIRECTORY)/, $^)


all-rs: pulsetutorial-array.rs pulsetutorial-loops.rs pulsetutorial-algorithms.rs

test: all-rs
	cargo test

.PHONY: test