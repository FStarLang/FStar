PULSE_ROOT ?= ../../../../..
SRC := .
ROOTS := $(wildcard *.fst)
CACHE_DIR := $(PULSE_ROOT)/build/logical_atomicity/cached_wait_free/_cache
OUTPUT_DIR := $(PULSE_ROOT)/build/logical_atomicity/cached_wait_free/_output
TAG := logical_atomicity_cached_wait_free
INCLUDE_PATHS += ../msqueue
OTHERFLAGS += --include $(PULSE_ROOT)/lib/core
OTHERFLAGS += --include $(PULSE_ROOT)/build/lib.core.checked
DEPFLAGS += --already_cached '*,-Pulse.Lib.LogicalAtomicity.Example'
include $(PULSE_ROOT)/mk/boot.mk
.DEFAULT_GOAL := all

$(OUTPUT_DIR)/CachedWF.ml: $(ALL_CHECKED_FILES)
	$(FSTAR_EXE) --silent --include $(CACHE_DIR) --include ../msqueue Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Clients.fst --codegen OCaml --custard_entry_module Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Clients -o $@

$(OUTPUT_DIR)/runtime.exe: $(OUTPUT_DIR)/CachedWF.ml CachedWF_atomics.ml runtime_test.ml
	cp CachedWF_atomics.ml runtime_test.ml $(OUTPUT_DIR)/
	cd $(OUTPUT_DIR) && $(FSTAR_EXE) --ocamlopt -I . CachedWF_atomics.ml CachedWF.ml runtime_test.ml -o runtime.exe

.PHONY: runtime-test
runtime-test: $(OUTPUT_DIR)/runtime.exe
	$<

all: verify runtime-test
