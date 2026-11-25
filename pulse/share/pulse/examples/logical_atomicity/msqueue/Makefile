# Keep queue proof and extraction artifacts separate from the other examples.
PULSE_ROOT ?= ../../../../..
SRC := .
ROOTS := $(wildcard *.fst)
CACHE_DIR := $(PULSE_ROOT)/build/logical_atomicity/msqueue/_cache
OUTPUT_DIR := $(PULSE_ROOT)/build/logical_atomicity/msqueue/_output
TAG := logical_atomicity_msqueue
OTHERFLAGS += --include $(PULSE_ROOT)/lib/core
OTHERFLAGS += --include $(PULSE_ROOT)/build/lib.core.checked
DEPFLAGS += --already_cached '*,-Pulse.Lib.LogicalAtomicity.Example'
include $(PULSE_ROOT)/mk/boot.mk
.DEFAULT_GOAL := all

# Extraction deliberately excludes lib/core: select installed/native realizations.
$(OUTPUT_DIR)/MSQueueClients.ml: $(ALL_CHECKED_FILES)
	$(FSTAR_EXE) --silent --include $(CACHE_DIR) Pulse.Lib.LogicalAtomicity.Example.MSQueue.Clients.fst --codegen OCaml --custard_entry_module Pulse.Lib.LogicalAtomicity.Example.MSQueue.Clients -o $@

$(OUTPUT_DIR)/MSQueueConcurrent.ml: $(ALL_CHECKED_FILES)
	$(FSTAR_EXE) --silent --include $(CACHE_DIR) Pulse.Lib.LogicalAtomicity.Example.MSQueue.Concurrent.fst --codegen OCaml --custard_entry_module Pulse.Lib.LogicalAtomicity.Example.MSQueue.Concurrent -o $@

# Queue atomics have their own mutex-backed boundary documented in that file.
REALIZATIONS := $(PULSE_ROOT)/lib/pulse/lib/ml/Pulse_Lib_SpinLock.ml \
	$(PULSE_ROOT)/test/pool/pulse_task/ml/Pulse_Lib_Core.ml \
	$(PULSE_ROOT)/test/pool/pulse_task/ml/Pulse_Lib_Sleep.ml \
	MSQueue_atomics.ml
RUNTIME_MODULES := MSQueueClients.ml MSQueueConcurrent.ml

$(OUTPUT_DIR)/runtime.exe: runtime_test.ml $(addprefix $(OUTPUT_DIR)/,$(RUNTIME_MODULES)) $(REALIZATIONS)
	cp runtime_test.ml $(REALIZATIONS) $(OUTPUT_DIR)/
	cd $(OUTPUT_DIR) && $(FSTAR_EXE) --ocamlopt -I . $(notdir $(REALIZATIONS)) $(RUNTIME_MODULES) runtime_test.ml -o runtime.exe

.PHONY: runtime-test
runtime-test: $(OUTPUT_DIR)/runtime.exe
	$<

all: verify runtime-test
