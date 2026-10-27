PULSE_ROOT ?= ../../../..
SRC := .
ROOTS := $(wildcard *.fst)
CACHE_DIR := $(PULSE_ROOT)/build/logical_atomicity/_cache
OUTPUT_DIR := $(PULSE_ROOT)/build/logical_atomicity/_output
TAG := logical_atomicity
OTHERFLAGS += --include $(PULSE_ROOT)/lib/core
OTHERFLAGS += --include $(PULSE_ROOT)/build/lib.core.checked
DEPFLAGS += --already_cached '*,-Pulse.Lib.LogicalAtomicity.Example'
include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := all

$(OUTPUT_DIR)/Counter.ml: $(ALL_CHECKED_FILES)
	$(FSTAR_EXE) --silent --include $(CACHE_DIR) Pulse.Lib.LogicalAtomicity.Example.Counter.fst --codegen OCaml --custard_entry_module Pulse.Lib.LogicalAtomicity.Example.Counter -o $@

$(OUTPUT_DIR)/Read.ml: $(ALL_CHECKED_FILES)
	$(FSTAR_EXE) --silent --include $(CACHE_DIR) Pulse.Lib.LogicalAtomicity.Example.Read.fst --codegen OCaml --custard_entry_module Pulse.Lib.LogicalAtomicity.Example.Read -o $@

$(OUTPUT_DIR)/Helping.ml: $(ALL_CHECKED_FILES)
	$(FSTAR_EXE) --silent --include $(CACHE_DIR) Pulse.Lib.LogicalAtomicity.Example.Helping.fst --codegen OCaml --custard_entry_module Pulse.Lib.LogicalAtomicity.Example.Helping -o $@

REALIZATIONS := $(PULSE_ROOT)/lib/pulse/lib/ml/Pulse_Lib_SpinLock.ml \
	$(PULSE_ROOT)/test/pool/pulse_task/ml/Pulse_Lib_Core.ml \
	$(PULSE_ROOT)/test/pool/pulse_task/ml/Pulse_Lib_Sleep.ml

$(OUTPUT_DIR)/runtime.exe: runtime_test.ml $(OUTPUT_DIR)/Counter.ml $(OUTPUT_DIR)/Read.ml $(OUTPUT_DIR)/Helping.ml $(REALIZATIONS)
	cp runtime_test.ml $(REALIZATIONS) $(OUTPUT_DIR)/
	cd $(OUTPUT_DIR) && $(FSTAR_EXE) --ocamlopt -I . $(notdir $(REALIZATIONS)) Counter.ml Read.ml Helping.ml runtime_test.ml -o runtime.exe

.PHONY: runtime-test
runtime-test: $(OUTPUT_DIR)/runtime.exe
	$<

all: verify runtime-test
