# Verify the examples, extract executable clients, and run native regressions.
# This directory is reached by the parent examples all/verify/clean targets.
# Foundation sources remain in lib/pulse/logical_atomicity and are installed
# by make 3; examples are not part of the installed library namespace search.
PULSE_ROOT ?= ../../../..
SRC := .
ROOTS := $(wildcard *.fst)
# Keep proof/extraction artifacts out of both source trees. The shared tag
# gives dependency analysis a separate cache from the installed Pulse library.
CACHE_DIR := $(PULSE_ROOT)/build/logical_atomicity/_cache
OUTPUT_DIR := $(PULSE_ROOT)/build/logical_atomicity/_output
TAG := logical_atomicity
# Verification of semantic wrappers needs core definitions. Do NOT pass these
# includes to extraction: it must select native realizations, not core models.
OTHERFLAGS += --include $(PULSE_ROOT)/lib/core
OTHERFLAGS += --include $(PULSE_ROOT)/build/lib.core.checked
# Installed foundations are dependencies, not additional example build roots.
DEPFLAGS += --already_cached '*,-Pulse.Lib.LogicalAtomicity.Example'
include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := all

# Whole-program extraction retains runtime operations and erases AU/mask proofs.
# Depend on all checks so neither rejection tests nor target/model wrappers
# can be silently skipped when requesting the runtime executable.
$(OUTPUT_DIR)/Counter.ml: $(ALL_CHECKED_FILES)
	$(FSTAR_EXE) --silent --include $(CACHE_DIR) Pulse.Lib.LogicalAtomicity.Example.Counter.fst --codegen OCaml --custard_entry_module Pulse.Lib.LogicalAtomicity.Example.Counter -o $@

$(OUTPUT_DIR)/Read.ml: $(ALL_CHECKED_FILES)
	$(FSTAR_EXE) --silent --include $(CACHE_DIR) Pulse.Lib.LogicalAtomicity.Example.Read.fst --codegen OCaml --custard_entry_module Pulse.Lib.LogicalAtomicity.Example.Read -o $@

$(OUTPUT_DIR)/Helping.ml: $(ALL_CHECKED_FILES)
	$(FSTAR_EXE) --silent --include $(CACHE_DIR) Pulse.Lib.LogicalAtomicity.Example.Helping.fst --codegen OCaml --custard_entry_module Pulse.Lib.LogicalAtomicity.Example.Helping -o $@

# Reuse the task tests' native fork/sleep and the library lock realization.
REALIZATIONS := $(PULSE_ROOT)/lib/pulse/lib/ml/Pulse_Lib_SpinLock.ml \
	$(PULSE_ROOT)/test/pool/pulse_task/ml/Pulse_Lib_Core.ml \
	$(PULSE_ROOT)/test/pool/pulse_task/ml/Pulse_Lib_Sleep.ml

RUNTIME_MODULES := Counter.ml Read.ml Helping.ml

# Copy handwritten modules into the output directory so OCaml intermediates
# never appear beside sources; compile against this compiler's runtime.
$(OUTPUT_DIR)/runtime.exe: runtime_test.ml $(addprefix $(OUTPUT_DIR)/,$(RUNTIME_MODULES)) $(REALIZATIONS)
	cp runtime_test.ml $(REALIZATIONS) $(OUTPUT_DIR)/
	cd $(OUTPUT_DIR) && $(FSTAR_EXE) --ocamlopt -I . $(notdir $(REALIZATIONS)) $(RUNTIME_MODULES) runtime_test.ml -o runtime.exe

# Runtime success supplements, rather than replaces, verified F* contracts.
.PHONY: runtime-test
runtime-test: $(OUTPUT_DIR)/runtime.exe
	$<

# Keep all's recursion separate from verify's recursion, avoiding two concurrent
# make processes writing a child's proof cache for a single all invocation.
.PHONY: concurrent-set-verify concurrent-set-runtime concurrent-set-clean
concurrent-set-verify:
	$(MAKE) -C concurrent_set verify
concurrent-set-runtime:
	$(MAKE) -C concurrent_set runtime-test
concurrent-set-clean:
	$(MAKE) -C concurrent_set clean
.PHONY: msqueue-verify msqueue-runtime msqueue-clean
msqueue-verify:
	$(MAKE) -C msqueue verify
msqueue-runtime:
	$(MAKE) -C msqueue runtime-test
msqueue-clean:
	$(MAKE) -C msqueue clean
.PHONY: cached-wait-free-verify cached-wait-free-runtime cached-wait-free-clean
cached-wait-free-verify:
	$(MAKE) -C cached_wait_free verify
cached-wait-free-runtime:
	$(MAKE) -C cached_wait_free runtime-test
cached-wait-free-clean:
	$(MAKE) -C cached_wait_free clean
verify: concurrent-set-verify msqueue-verify cached-wait-free-verify
runtime-test: concurrent-set-runtime msqueue-runtime cached-wait-free-runtime
clean: concurrent-set-clean msqueue-clean cached-wait-free-clean
all: all-checked runtime-test
