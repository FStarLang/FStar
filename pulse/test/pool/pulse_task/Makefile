PULSE_ROOT ?= ../../..
ifndef STAGE3 # Only if not testing F* stage3
OTHERFLAGS += --include $(PULSE_ROOT)/out/lib/pulse
endif
OTHERFLAGS += --include $(PULSE_ROOT)/share/pulse/examples

CACHE_DIR  := _cache
OUTPUT_DIR := _output
SRC        := .
ROOTS      := Quicksort.Task.fst
TAG        := pool

include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := all

.PHONY: all
all: test

# Custard is whole-program: one run from the entry point emits the task pool,
# the quicksort and everything they reach as a single .ml file, so there is no
# per-module extraction and no --extract list.  See doc/ref/custard.md 128.
$(OUTPUT_DIR)/Quicksort_Task.ml: $(ALL_CHECKED_FILES)
	$(call msg, "CUSTARD", Quicksort.Task)
	$(Q)mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) --already_cached '*,' --codegen OCaml \
	  --custard_entry Quicksort.Task.quicksort \
	  $(CACHE_DIR)/Quicksort.Task.fst.checked -o $@

# Pulse.Lib.SpinLock must never be compiled from its F* source: its cas is a
# specification, and the compiled lock locks nothing.  Custard treats the
# module as realized (section 128) and this is the realization; the other two
# are the primitives Pulse declares and does not define.
REALIZATIONS := $(PULSE_ROOT)/lib/pulse/lib/ml/Pulse_Lib_SpinLock.ml \
                ml/Pulse_Lib_Core.ml ml/Pulse_Lib_Sleep.ml

# Copied into the output directory rather than compiled where they lie: a
# realization's .cmi has to sit on the include path of the generated module
# that refers to it, and there is only one include path here.
$(OUTPUT_DIR)/qsort.exe: $(OUTPUT_DIR)/Quicksort_Task.ml $(REALIZATIONS) driver.ml
	$(call msg, "OCAMLOPT", qsort.exe)
	$(Q)cp -p $(REALIZATIONS) driver.ml $(OUTPUT_DIR)/
	$(Q)cd $(OUTPUT_DIR) && $(FSTAR_EXE) --ocamlopt -I . \
	  $(notdir $(REALIZATIONS)) Quicksort_Task.ml driver.ml -o $(notdir $@)

.PHONY: test
test: run
ifeq ($(NOCHERRY),)
test: run-cherry
endif

.PHONY: run
run: $(OUTPUT_DIR)/qsort.exe
	$(Q)$<

# The same program through Cherry (doc/ref/cherry.md), the reference-counted
# C backend: Pulse.Lib.SpinLock's realization is the C one the DICE example
# uses, c/ has the other primitives (fork_core is a detached pthread) and the
# driver.  NOCHERRY=1 leaves it out of `test`.
CHERRY_INC    = $(shell $(FSTAR_EXE) --locate_lib)/ulib/c
CHERRY_LOCK   := $(PULSE_ROOT)/share/pulse/examples/dice/external/c/hacl
CHERRY_CC     ?= $(CC)
CHERRY_CFLAGS ?= -std=c11 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined

$(OUTPUT_DIR)/cherry/Quicksort_Task.c: $(ALL_CHECKED_FILES)
	$(call msg, "CHERRY", Quicksort.Task)
	$(Q)mkdir -p $(dir $@)
	$(Q)$(FSTAR) --already_cached '*,' --codegen Cherry \
	  --custard_monomorphize_types true \
	  --custard_entry Quicksort.Task.quicksort \
	  $(CACHE_DIR)/Quicksort.Task.fst.checked -o $@

$(OUTPUT_DIR)/cherry/qsort.exe: $(OUTPUT_DIR)/cherry/Quicksort_Task.c c/Pulse_Lib_Core.c c/driver.c
	$(call msg, "CC CHERRY", qsort.exe)
	$(Q)$(CHERRY_CC) $(CHERRY_CFLAGS) -pthread -I$(CHERRY_INC) -I$(CHERRY_LOCK) \
	  -I$(dir $@) $< c/Pulse_Lib_Core.c c/driver.c \
	  $(CHERRY_LOCK)/Pulse_Lib_SpinLock.c $(CHERRY_INC)/cherry.c -o $@

.PHONY: run-cherry
run-cherry: $(OUTPUT_DIR)/cherry/qsort.exe
	$(Q)$<

# Here so `make accept` works from the parent dir
.PHONY: accept
accept:
