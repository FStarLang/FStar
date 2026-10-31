# Keep this example's proof and extraction artifacts separate from the FIFO.
PULSE_ROOT ?= ../../../../..
SRC := .
ROOTS := $(wildcard *.fst)
CACHE_DIR := $(PULSE_ROOT)/build/logical_atomicity/concurrent_set/_cache
OUTPUT_DIR := $(PULSE_ROOT)/build/logical_atomicity/concurrent_set/_output
TAG := logical_atomicity_concurrent_set
OTHERFLAGS += --include $(PULSE_ROOT)/lib/core
OTHERFLAGS += --include $(PULSE_ROOT)/build/lib.core.checked
# Only the generic MSQueue.Actions combinators are shared with the queue.
INCLUDE_PATHS += ../msqueue
DEPFLAGS += --already_cached '*,-Pulse.Lib.LogicalAtomicity.Example'
include $(PULSE_ROOT)/mk/boot.mk
.DEFAULT_GOAL := all

# Extraction deliberately excludes lib/core: use the installed native runtime.
$(OUTPUT_DIR)/SetClients.ml: $(ALL_CHECKED_FILES)
	$(FSTAR_EXE) --silent --include ../msqueue --include $(CACHE_DIR) Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Clients.fst --codegen OCaml --custard_entry_module Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Clients -o $@

$(OUTPUT_DIR)/SetConcurrent.ml: $(ALL_CHECKED_FILES)
	$(FSTAR_EXE) --silent --include ../msqueue --include $(CACHE_DIR) Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Concurrent.fst --codegen OCaml --custard_entry_module Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Concurrent -o $@

$(OUTPUT_DIR)/SetShared.ml: $(ALL_CHECKED_FILES)
	$(FSTAR_EXE) --silent --include ../msqueue --include $(CACHE_DIR) Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Shared.fst --codegen OCaml --custard_entry_module Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Shared -o $@

REALIZATIONS := $(PULSE_ROOT)/lib/pulse/lib/ml/Pulse_Lib_SpinLock.ml \
	$(PULSE_ROOT)/test/pool/pulse_task/ml/Pulse_Lib_Core.ml \
	$(PULSE_ROOT)/test/pool/pulse_task/ml/Pulse_Lib_Sleep.ml
RUNTIME_MODULES := SetClients.ml SetConcurrent.ml SetShared.ml

$(OUTPUT_DIR)/runtime.exe: runtime_test.ml $(addprefix $(OUTPUT_DIR)/,$(RUNTIME_MODULES)) $(REALIZATIONS)
	cp runtime_test.ml $(REALIZATIONS) $(OUTPUT_DIR)/
	cd $(OUTPUT_DIR) && $(FSTAR_EXE) --ocamlopt -I . $(notdir $(REALIZATIONS)) $(RUNTIME_MODULES) runtime_test.ml -o runtime.exe

.PHONY: runtime-test
runtime-test: $(OUTPUT_DIR)/runtime.exe
	$<

all: verify runtime-test
